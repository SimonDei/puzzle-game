/* Jigsaw — vanilla HTML/CSS/JS grid puzzle.
   World coordinates are image pixels: the solution area is exactly imgW x imgH.
   The camera maps world -> screen: screen = world * scale + cam. */
(function () {
  'use strict';

  var SAVE_KEY = 'jigsaw.v1';
  var SCATTER = 2.6;     // board size as a multiple of the image size
  var MAX_DIM = 2600;      // longest edge kept from the upload
  var MAX_PIXELS = 4.5e6;  // and an area cap, so panoramas stay affordable
  var SAVE_CHARS = 2.0e6;  // rough localStorage headroom for the stored photo
  var PHOTO_STORE = 'photos';
  var TARGETS = [50, 100, 200, 300, 500];
  var NB = [[1, 0], [-1, 0], [0, 1], [0, -1]];

  // One puzzle edge, as offsets along the edge (t, 0..1) and outward from it
  // (d, 1 = full tab depth). Both pieces sharing an edge trace this same curve,
  // one outward and one inward, so a tab always fits its blank exactly.
  var EDGE = [
    ['L', 0.40, 0],
    ['C', 0.45, 0, 0.34, 0.30, 0.34, 0.55],
    ['C', 0.34, 1.15, 0.66, 1.15, 0.66, 0.55],
    ['C', 0.66, 0.30, 0.55, 0, 0.60, 0],
    ['L', 1, 0]
  ];
  var TAB_DEPTH = 0.24;  // knob height, as a fraction of the shorter piece side

  var BACKGROUNDS = [
    { id: 'charcoal', name: 'Charcoal', color: '#22252b' },
    { id: 'slate', name: 'Slate', color: '#2f3d4d' },
    { id: 'walnut', name: 'Walnut', texture: 'wood' },
    { id: 'felt', name: 'Green felt', texture: 'felt' },
    { id: 'paper', name: 'Paper', texture: 'paper' }
  ];

  var $ = function (sel) { return document.querySelector(sel); };

  var el = {
    upload: $('#screen-upload'), setup: $('#screen-setup'), game: $('#screen-game'),
    file: $('#file-input'), drop: $('#dropzone'), uploadErr: $('#upload-error'),
    setupPreview: $('#setup-preview'), countList: $('#count-list'),
    setupBack: $('#setup-back'), setupStart: $('#setup-start'),
    stage: $('#stage'), canvas: $('#board'),
    timer: $('#timer'), pause: $('#btn-pause'), counter: $('#counter'), bar: $('#bar-fill'),
    bgSelect: $('#bg-select'), btnThumb: $('#btn-thumb'), btnSound: $('#btn-sound'),
    btnNew: $('#btn-new'), zoomIn: $('#btn-zoom-in'), zoomOut: $('#btn-zoom-out'), fit: $('#btn-fit'),
    thumb: $('#thumb'), thumbImg: $('#thumb-img'), thumbClose: $('#thumb-close'),
    thumbBar: $('#thumb-bar'),
    veil: $('#paused-veil'), done: $('#complete'), finalTime: $('#final-time'),
    finalPieces: $('#final-pieces'), btnAdmire: $('#btn-admire'), btnDoneNew: $('#btn-complete-new'),
    btnSummary: $('#btn-summary'), toast: $('#toast')
  };

  var ctx = el.canvas.getContext('2d');

  /* ------------------------------------------------------------------ state */

  var S = {
    img: null, imgData: '', saveData: '', saveScale: 1, imgInIdb: false, imgW: 0, imgH: 0,
    cols: 0, rows: 0, pw: 0, ph: 0,
    boardW: 0, boardH: 0, solX: 0, solY: 0,
    pieces: [], grid: [], zOrder: [], groups: new Map(), nextGid: 1,
    placed: 0, elapsed: 0, running: false, complete: false,
    cam: { x: 0, y: 0, scale: 1 },
    bg: 'slate', sound: true, showThumb: true, thumbPos: null,
    doneGlow: 0
  };

  var pending = null;        // {dataURL, w, h, img} chosen on the setup screen
  var pendingTarget = 200;
  var anim = new Set();      // pieces with a non-zero visual offset
  var dirty = true;
  var saveTimer = 0;
  var vw = 0, vh = 0, dpr = 1;

  /* ------------------------------------------------------------- small utils */

  function show(screen) {
    el.upload.hidden = screen !== 'upload';
    el.setup.hidden = screen !== 'setup';
    el.game.hidden = screen !== 'game';
    if (screen === 'game') resize();
  }

  function fmtTime(ms) {
    var t = Math.floor(ms / 1000);
    var h = Math.floor(t / 3600), m = Math.floor(t / 60) % 60, s = t % 60;
    var pad = function (n) { return (n < 10 ? '0' : '') + n; };
    return (h ? h + ':' + pad(m) : pad(m)) + ':' + pad(s);
  }

  var toastTimer = 0;
  function toast(msg) {
    clearTimeout(toastTimer);
    if (!msg) { el.toast.hidden = true; return; }
    el.toast.textContent = msg;
    el.toast.hidden = false;
    toastTimer = setTimeout(function () { el.toast.hidden = true; }, 3200);
  }

  /* -------------------------------------------------------------------- audio */

  var ac = null;
  function blip(freq, dur, gain) {
    if (!S.sound) return;
    try {
      var Ctor = window.AudioContext || window.webkitAudioContext;
      if (!Ctor) return;
      ac = ac || new Ctor();
      var o = ac.createOscillator(), g = ac.createGain(), t = ac.currentTime;
      o.type = 'triangle';
      o.frequency.setValueAtTime(freq, t);
      g.gain.setValueAtTime(0.0001, t);
      g.gain.exponentialRampToValueAtTime(gain, t + 0.008);
      g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
      o.connect(g); g.connect(ac.destination);
      o.start(t); o.stop(t + dur + 0.03);
    } catch (e) { /* audio is optional */ }
  }
  function playSnap() { blip(620, 0.08, 0.10); }
  function playAnchor() { blip(880, 0.11, 0.12); }
  function playDone() {
    [523, 659, 784, 1046].forEach(function (f, i) {
      setTimeout(function () { blip(f, 0.3, 0.11); }, i * 140);
    });
  }

  /* ---------------------------------------------------------------- textures */

  var patterns = {};
  function pattern(id) {
    if (patterns[id]) return patterns[id];
    var c = document.createElement('canvas'), g;
    if (id === 'wood') {
      c.width = 180; c.height = 180;
      g = c.getContext('2d');
      g.fillStyle = '#6d4a2c'; g.fillRect(0, 0, 180, 180);
      for (var x = 0; x < 180; x++) {
        var v = Math.sin(x * 0.42) * 0.5 + Math.sin(x * 0.11) * 0.5;
        var light = v + (Math.random() - 0.5) * 0.7 > 0;
        g.fillStyle = light ? 'rgba(255,220,180,' + (0.02 + Math.random() * 0.05) + ')'
                            : 'rgba(40,20,6,' + (0.03 + Math.random() * 0.07) + ')';
        g.fillRect(x, 0, 1, 180);
      }
    } else if (id === 'felt' || id === 'paper') {
      c.width = 128; c.height = 128;
      g = c.getContext('2d');
      g.fillStyle = id === 'felt' ? '#2f6b48' : '#e7e1d4';
      g.fillRect(0, 0, 128, 128);
      var d = g.getImageData(0, 0, 128, 128), px = d.data, amp = id === 'felt' ? 16 : 10;
      for (var i = 0; i < px.length; i += 4) {
        var n = (Math.random() - 0.5) * amp;
        px[i] += n; px[i + 1] += n; px[i + 2] += n;
      }
      g.putImageData(d, 0, 0);
    }
    patterns[id] = ctx.createPattern(c, 'repeat');
    return patterns[id];
  }

  function bgDef() {
    for (var i = 0; i < BACKGROUNDS.length; i++) if (BACKGROUNDS[i].id === S.bg) return BACKGROUNDS[i];
    return BACKGROUNDS[0];
  }

  /* ------------------------------------------------------------ image intake */

  function loadImage(src) {
    return new Promise(function (res, rej) {
      var im = new Image();
      im.onload = function () { res(im); };
      im.onerror = function () { rej(new Error('bad image')); };
      im.src = src;
    });
  }

  function readFile(file) {
    return new Promise(function (res, rej) {
      var fr = new FileReader();
      fr.onload = function () { res(fr.result); };
      fr.onerror = function () { rej(new Error('read failed')); };
      fr.readAsDataURL(file);
    });
  }

  // Downscale to a sane size and re-encode as JPEG so it fits in localStorage.
  function normalize(img) {
    var w = img.naturalWidth, h = img.naturalHeight;
    var k = Math.min(1, MAX_DIM / Math.max(w, h), Math.sqrt(MAX_PIXELS / (w * h)));
    w = Math.max(1, Math.round(w * k));
    h = Math.max(1, Math.round(h * k));
    var c = document.createElement('canvas');
    c.width = w; c.height = h;
    var g = c.getContext('2d');
    g.imageSmoothingQuality = 'high';
    g.drawImage(img, 0, 0, w, h);
    return { dataURL: c.toDataURL('image/jpeg', 0.9), w: w, h: h };
  }

  function handleFile(file) {
    el.uploadErr.hidden = true;
    if (!file || !/^image\//.test(file.type)) {
      el.uploadErr.textContent = 'That file is not an image. Please pick a PNG or JPEG.';
      el.uploadErr.hidden = false;
      return;
    }
    readFile(file).then(loadImage).then(function (img) {
      var norm = normalize(img);
      return loadImage(norm.dataURL).then(function (small) {
        pending = { dataURL: norm.dataURL, w: norm.w, h: norm.h, img: small };
        openSetup();
      });
    }).catch(function () {
      el.uploadErr.textContent = 'Could not read that image. Try another file.';
      el.uploadErr.hidden = false;
    });
  }

  /* ------------------------------------------------------------- grid choice */

  // Grid whose piece count is near the target and whose pieces are near-square.
  function gridFor(target, w, h) {
    var aspect = w / h, best = null;
    var max = Math.ceil(Math.sqrt(target * 2) * Math.max(aspect, 1 / aspect)) + 4;
    for (var rows = 1; rows <= max; rows++) {
      for (var cols = 1; cols <= max; cols++) {
        var count = cols * rows;
        if (count < target * 0.6 || count > target * 1.5) continue;
        var pieceAspect = (w / cols) / (h / rows);
        var score = Math.abs(count - target) / target * 3 + Math.abs(Math.log(pieceAspect));
        if (!best || score < best.score) best = { cols: cols, rows: rows, count: count, score: score };
      }
    }
    return best || { cols: 10, rows: 10, count: 100 };
  }

  function openSetup() {
    el.setupPreview.src = pending.dataURL;
    el.countList.innerHTML = '';
    TARGETS.forEach(function (t) {
      var g = gridFor(t, pending.w, pending.h);
      var b = document.createElement('button');
      b.className = 'count' + (t === pendingTarget ? ' active' : '');
      b.innerHTML = '<b>' + t + ' pieces</b><small>' + g.cols + ' × ' + g.rows +
                    ' grid — ' + g.count + ' pieces</small>';
      b.addEventListener('click', function () {
        pendingTarget = t;
        Array.prototype.forEach.call(el.countList.children, function (c) { c.classList.remove('active'); });
        b.classList.add('active');
      });
      el.countList.appendChild(b);
    });
    show('setup');
  }

  /* ------------------------------------------------------------ puzzle setup */

  function groupOf(p) { return S.groups.get(p.gid); }
  function pieceAt(col, row) {
    if (col < 0 || row < 0 || col >= S.cols || row >= S.rows) return null;
    return S.grid[row * S.cols + col];
  }

  // Trace one edge from (ox,oy) along unit vector (ux,uy); the outward normal is
  // (uy,-ux) because pieces are traced clockwise from their top-left corner.
  function addEdge(path, ox, oy, ux, uy, len, s) {
    var nx = uy, ny = -ux, i, seg;
    function at(t, d) {
      return [ox + ux * t * len + nx * d * S.tab * s, oy + uy * t * len + ny * d * S.tab * s];
    }
    if (!s) { var flat = at(1, 0); path.lineTo(flat[0], flat[1]); return; }
    for (i = 0; i < EDGE.length; i++) {
      seg = EDGE[i];
      if (seg[0] === 'L') {
        var a = at(seg[1], seg[2]);
        path.lineTo(a[0], a[1]);
      } else {
        var c1 = at(seg[1], seg[2]), c2 = at(seg[3], seg[4]), e = at(seg[5], seg[6]);
        path.bezierCurveTo(c1[0], c1[1], c2[0], c2[1], e[0], e[1]);
      }
    }
  }

  function edgePath(p, side) {
    var path = new Path2D();
    if (side === 0) { path.moveTo(0, 0); addEdge(path, 0, 0, 1, 0, S.pw, p.e[0]); }
    if (side === 1) { path.moveTo(S.pw, 0); addEdge(path, S.pw, 0, 0, 1, S.ph, p.e[1]); }
    if (side === 2) { path.moveTo(S.pw, S.ph); addEdge(path, S.pw, S.ph, -1, 0, S.pw, p.e[2]); }
    if (side === 3) { path.moveTo(0, S.ph); addEdge(path, 0, S.ph, 0, -1, S.ph, p.e[3]); }
    return path;
  }

  function piecePath(p) {
    var path = new Path2D();
    path.moveTo(0, 0);
    addEdge(path, 0, 0, 1, 0, S.pw, p.e[0]);
    addEdge(path, S.pw, 0, 0, 1, S.ph, p.e[1]);
    addEdge(path, S.pw, S.ph, -1, 0, S.pw, p.e[2]);
    addEdge(path, 0, S.ph, 0, -1, S.ph, p.e[3]);
    path.closePath();
    return path;
  }

  // Cut every piece once into a single sprite atlas. Drawing a frame is then
  // one drawImage per piece, with no clipping work per frame.
  function buildAtlas() {
    S.tab = Math.min(S.pw, S.ph) * TAB_DEPTH;
    S.margin = Math.ceil(S.tab + 1);
    S.cw = Math.ceil(S.pw + S.margin * 2);
    S.ch = Math.ceil(S.ph + S.margin * 2);
    var atlas = document.createElement('canvas');
    atlas.width = S.cw * S.cols;
    atlas.height = S.ch * S.rows;
    var g = atlas.getContext('2d');
    g.imageSmoothingQuality = 'high';
    // a resumed puzzle may carry a photo saved at reduced size; world
    // coordinates stay in original image pixels either way
    var k = S.img.naturalWidth ? S.img.naturalWidth / S.imgW : 1;
    for (var i = 0; i < S.pieces.length; i++) {
      var p = S.pieces[i];
      p.path = piecePath(p);
      p.edges = [edgePath(p, 0), edgePath(p, 1), edgePath(p, 2), edgePath(p, 3)];
      p.sx = p.col * S.cw;
      p.sy = p.row * S.ch;
      g.save();
      g.translate(p.sx + S.margin, p.sy + S.margin);
      g.save();
      g.clip(p.path);
      // copy only this cell's slice of the photo, clamped to the image
      var sx0 = p.col * S.pw - S.margin, sy0 = p.row * S.ph - S.margin;
      var cx = Math.max(0, sx0), cy = Math.max(0, sy0);
      var cw = Math.min(S.imgW, sx0 + S.cw) - cx, ch = Math.min(S.imgH, sy0 + S.ch) - cy;
      if (cw > 0 && ch > 0) {
        g.drawImage(S.img, cx * k, cy * k, cw * k, ch * k,
                    cx - p.col * S.pw, cy - p.row * S.ph, cw, ch);
      }
      g.lineWidth = Math.max(2, S.tab * 0.3);         // rim shading, inside only
      g.strokeStyle = 'rgba(0,0,0,.20)';
      g.stroke(p.path);
      g.translate(1.2, 1.2);                          // lit top-left bevel
      g.lineWidth = 1.5;
      g.strokeStyle = 'rgba(255,255,255,.28)';
      g.stroke(p.path);
      g.restore();
      g.lineWidth = 1;
      g.strokeStyle = 'rgba(0,0,0,.45)';
      g.stroke(p.path);
      g.restore();
    }
    S.atlas = atlas;
  }

  // Tab directions live on the shared edges, so neighbours always agree.
  // "1" on a vertical edge means the tab points right; on a horizontal one, down.
  function edgeSigns(saved, n) {
    var out = new Array(n), i;
    var usable = typeof saved === 'string' && saved.length === n;
    for (i = 0; i < n; i++) {
      out[i] = usable ? (saved.charAt(i) === '1' ? 1 : -1) : (Math.random() < 0.5 ? 1 : -1);
    }
    return out;
  }
  function encodeSigns(a) {
    var out = '';
    for (var i = 0; i < a.length; i++) out += a[i] > 0 ? '1' : '0';
    return out;
  }

  function buildPieces(savedEdges) {
    S.pw = S.imgW / S.cols;
    S.ph = S.imgH / S.rows;
    S.boardW = S.imgW * SCATTER;
    S.boardH = S.imgH * SCATTER;
    S.solX = (S.boardW - S.imgW) / 2;
    S.solY = (S.boardH - S.imgH) / 2;
    S.pieces = []; S.grid = []; S.groups = new Map(); S.nextGid = 1;
    S.groups.set(0, { id: 0, anchored: true, pieces: [] });
    var saved = savedEdges || {};
    S.vs = edgeSigns(saved.v, (S.cols - 1) * S.rows);
    S.hs = edgeSigns(saved.h, S.cols * (S.rows - 1));
    for (var r = 0; r < S.rows; r++) {
      for (var c = 0; c < S.cols; c++) {
        var e = [
          r > 0 ? -S.hs[(r - 1) * S.cols + c] : 0,
          c < S.cols - 1 ? S.vs[r * (S.cols - 1) + c] : 0,
          r < S.rows - 1 ? S.hs[r * S.cols + c] : 0,
          c > 0 ? -S.vs[r * (S.cols - 1) + c - 1] : 0
        ];
        var p = { i: S.pieces.length, col: c, row: r, x: 0, y: 0, gid: S.nextGid++, ax: 0, ay: 0, e: e };
        S.groups.set(p.gid, { id: p.gid, anchored: false, pieces: [p] });
        S.grid[r * S.cols + c] = p;
        S.pieces.push(p);
      }
    }
    S.zOrder = S.pieces.slice();
    for (var i = S.zOrder.length - 1; i > 0; i--) {
      var j = Math.floor(Math.random() * (i + 1));
      var t = S.zOrder[i]; S.zOrder[i] = S.zOrder[j]; S.zOrder[j] = t;
    }
    S.placed = 0;
    anim.clear();
    buildAtlas();
  }

  // Drop every piece anywhere on the table, the solution area included.
  // A piece never starts within snapping distance of its own slot, so nothing
  // looks placed before the player has touched it.
  function scatter() {
    var spanX = S.boardW - S.pw, spanY = S.boardH - S.ph;
    var clear = Math.min(S.pw, S.ph);
    S.pieces.forEach(function (p) {
      var tx = S.solX + p.col * S.pw, ty = S.solY + p.row * S.ph;
      for (var tries = 0; tries < 8; tries++) {
        p.x = Math.random() * spanX;
        p.y = Math.random() * spanY;
        if (Math.hypot(p.x - tx, p.y - ty) > clear) break;
      }
    });
  }

  function startPuzzle(target) {
    var g = gridFor(target, pending.w, pending.h);
    S.img = pending.img;
    S.imgData = pending.dataURL;
    S.saveData = pending.dataURL;
    S.saveScale = 1;
    S.imgInIdb = false;
    saveBroken = false;
    S.imgW = pending.w; S.imgH = pending.h;
    S.cols = g.cols; S.rows = g.rows;
    buildPieces(null);
    scatter();
    S.elapsed = 0;
    S.running = true;
    S.complete = false;
    S.doneGlow = 0;
    el.thumbImg.src = S.imgData;
    el.done.hidden = true;
    el.btnSummary.hidden = true;
    show('game');
    fitView();
    syncChrome();
    updateHud();
    saveNow();
  }

  /* ------------------------------------------------------------------ camera */

  // The table has no edges. Fit is the way back: it frames the starting area
  // plus anything dragged beyond it, so nothing can be lost off-screen.
  function contentBounds() {
    var x0 = 0, y0 = 0, x1 = S.boardW || 1, y1 = S.boardH || 1;
    for (var i = 0; i < S.pieces.length; i++) {
      var p = S.pieces[i];
      if (p.x - S.margin < x0) x0 = p.x - S.margin;
      if (p.y - S.margin < y0) y0 = p.y - S.margin;
      if (p.x + S.pw + S.margin > x1) x1 = p.x + S.pw + S.margin;
      if (p.y + S.ph + S.margin > y1) y1 = p.y + S.ph + S.margin;
    }
    return { x: x0, y: y0, w: x1 - x0, h: y1 - y0 };
  }
  function fitScale() {
    var b = contentBounds();
    return Math.min(vw / b.w, vh / b.h) * 0.96;
  }
  function minScale() { return fitScale() * 0.7; }
  function maxScale() { return 4; }

  function fitView() {
    var b = contentBounds();
    S.cam.scale = Math.min(vw / b.w, vh / b.h) * 0.96;
    S.cam.x = (vw - b.w * S.cam.scale) / 2 - b.x * S.cam.scale;
    S.cam.y = (vh - b.h * S.cam.scale) / 2 - b.y * S.cam.scale;
    dirty = true;
  }

  function zoomAt(sx, sy, factor) {
    var next = Math.min(maxScale(), Math.max(minScale(), S.cam.scale * factor));
    if (next === S.cam.scale) return;
    var wx = (sx - S.cam.x) / S.cam.scale, wy = (sy - S.cam.y) / S.cam.scale;
    S.cam.scale = next;
    S.cam.x = sx - wx * next;
    S.cam.y = sy - wy * next;
    dirty = true;
    save();
  }

  function screenToWorld(sx, sy) {
    return { x: (sx - S.cam.x) / S.cam.scale, y: (sy - S.cam.y) / S.cam.scale };
  }

  /* -------------------------------------------------------------- group ops */

  function translateGroup(g, dx, dy) {
    for (var i = 0; i < g.pieces.length; i++) { g.pieces[i].x += dx; g.pieces[i].y += dy; }
  }

  function bringToFront(g) {
    var set = new Set(g.pieces);
    var rest = S.zOrder.filter(function (p) { return !set.has(p); });
    S.zOrder = rest.concat(g.pieces);
  }
  function sendToBack(pieces) {
    var set = new Set(pieces);
    var rest = S.zOrder.filter(function (p) { return !set.has(p); });
    S.zOrder = pieces.concat(rest);
  }

  function mergeInto(targetGid, srcGid) {
    var t = S.groups.get(targetGid), s = S.groups.get(srcGid);
    for (var i = 0; i < s.pieces.length; i++) { s.pieces[i].gid = targetGid; t.pieces.push(s.pieces[i]); }
    S.groups.delete(srcGid);
    bringToFront(t);
    return targetGid;
  }

  function anchorGroup(g) {
    var board = S.groups.get(0);
    for (var i = 0; i < g.pieces.length; i++) {
      var p = g.pieces[i];
      p.x = S.solX + p.col * S.pw;
      p.y = S.solY + p.row * S.ph;
      p.gid = 0;
      board.pieces.push(p);
    }
    if (g.id !== 0) S.groups.delete(g.id);
    sendToBack(board.pieces);
    S.placed = board.pieces.length;
  }

  function snapThreshold() {
    var small = Math.min(S.pw, S.ph);
    return Math.max(Math.min(small * 0.45, 10 / S.cam.scale), small * 0.22);
  }

  /* Try to lock a just-dropped group onto the board or onto its neighbours.
     Only correct joins are ever possible: every candidate is derived from the
     piece's true grid position, so nothing can snap into a wrong slot. */
  function trySnap(gid) {
    var before = new Map();
    S.pieces.forEach(function (p) { before.set(p, { x: p.x, y: p.y }); });

    var snapped = false, anchored = false;
    for (var iter = 0; iter < 16; iter++) {
      var g = S.groups.get(gid);
      if (!g || g.anchored) break;
      var t = snapThreshold(), best = null, i, k, p;

      for (i = 0; i < g.pieces.length; i++) {
        p = g.pieces[i];
        var tx = S.solX + p.col * S.pw, ty = S.solY + p.row * S.ph;
        var d = Math.hypot(tx - p.x, ty - p.y);
        if (d <= t && (!best || d < best.d)) best = { d: d, dx: tx - p.x, dy: ty - p.y, join: 0 };
      }
      for (i = 0; i < g.pieces.length; i++) {
        p = g.pieces[i];
        for (k = 0; k < NB.length; k++) {
          var n = pieceAt(p.col + NB[k][0], p.row + NB[k][1]);
          if (!n || n.gid === gid) continue;
          var nx = n.x - NB[k][0] * S.pw, ny = n.y - NB[k][1] * S.ph;
          var nd = Math.hypot(nx - p.x, ny - p.y);
          if (nd <= t && (!best || nd < best.d)) best = { d: nd, dx: nx - p.x, dy: ny - p.y, join: n.gid };
        }
      }
      if (!best) break;

      translateGroup(g, best.dx, best.dy);
      snapped = true;
      if (best.join === 0) { anchorGroup(g); anchored = true; break; }
      gid = mergeInto(best.join, gid);
    }

    // A fully assembled loose group settles into the solution area on its own.
    var fin = S.groups.get(gid);
    if (fin && !fin.anchored && fin.pieces.length === S.pieces.length) {
      anchorGroup(fin); snapped = true; anchored = true;
    }

    if (snapped) {
      S.pieces.forEach(function (p) {
        var b = before.get(p);
        if (b.x !== p.x || b.y !== p.y) { p.ax = b.x - p.x; p.ay = b.y - p.y; anim.add(p); }
      });
      dirty = true;
      if (anchored) playAnchor(); else playSnap();
      updateHud();
      if (S.placed === S.pieces.length) finish();
    }
    return snapped;
  }

  function finish() {
    S.complete = true;
    S.running = false;
    S.doneGlow = 1;
    el.finalTime.textContent = fmtTime(S.elapsed);
    el.finalPieces.textContent = String(S.pieces.length);
    el.done.hidden = false;
    el.btnSummary.hidden = true;
    el.veil.hidden = true;
    syncChrome();
    playDone();
    dirty = true;
    saveNow();
  }

  /* -------------------------------------------------------------------- HUD */

  function updateHud() {
    var total = S.pieces.length || 1;
    el.counter.textContent = S.placed + ' / ' + S.pieces.length + ' placed';
    el.bar.style.width = (S.placed / total * 100) + '%';
    el.timer.textContent = fmtTime(S.elapsed);
  }

  function syncChrome() {
    el.pause.innerHTML = S.running ? '&#10073;&#10073;' : '&#9654;';
    el.pause.disabled = S.complete;
    el.veil.hidden = S.running || S.complete || !S.img;
    el.thumb.hidden = !S.showThumb;
    applyThumbPos();
    el.btnThumb.classList.toggle('on', S.showThumb);
    el.btnSound.classList.toggle('on', S.sound);
    el.btnSound.innerHTML = S.sound ? '&#128266;' : '&#128263;';
    el.bgSelect.value = S.bg;
  }

  /* ------------------------------------------------------------------ render */

  function resize() {
    var r = el.stage.getBoundingClientRect();
    dpr = window.devicePixelRatio || 1;
    vw = Math.max(1, Math.round(r.width));
    vh = Math.max(1, Math.round(r.height));
    el.canvas.width = Math.round(vw * dpr);
    el.canvas.height = Math.round(vh * dpr);
    ctx.imageSmoothingQuality = 'high';   // resizing the canvas resets this
    applyThumbPos();
    dirty = true;
  }

  // Trace only the edges that face out of the cluster, tabs included.
  function strokeOutline(pieces, color, width) {
    var set = new Set(pieces.map(function (p) { return p.row * S.cols + p.col; }));
    ctx.strokeStyle = color;
    ctx.lineWidth = width;
    for (var i = 0; i < pieces.length; i++) {
      var p = pieces[i], k = p.row * S.cols + p.col;
      ctx.save();
      ctx.translate(p.x + p.ax, p.y + p.ay);
      if (!set.has(k - S.cols)) ctx.stroke(p.edges[0]);
      if (p.col === S.cols - 1 || !set.has(k + 1)) ctx.stroke(p.edges[1]);
      if (!set.has(k + S.cols)) ctx.stroke(p.edges[2]);
      if (p.col === 0 || !set.has(k - 1)) ctx.stroke(p.edges[3]);
      ctx.restore();
    }
  }

  function draw() {
    var def = bgDef();
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.fillStyle = def.texture ? pattern(def.texture) : def.color;
    ctx.fillRect(0, 0, vw, vh);
    if (!S.img) return;

    ctx.save();
    ctx.translate(S.cam.x, S.cam.y);
    ctx.scale(S.cam.scale, S.cam.scale);
    var inv = 1 / S.cam.scale;

    var vx0 = -S.cam.x * inv, vy0 = -S.cam.y * inv;
    var vx1 = vx0 + vw * inv, vy1 = vy0 + vh * inv;

    // A finished puzzle keeps its pieces: the seams you earned stay visible.
    // Completion only shows as a halo that fades out behind the assembled image.
    if (S.complete && S.doneGlow > 0) {
      ctx.save();
      ctx.shadowColor = 'rgba(120, 220, 170,' + (0.75 * S.doneGlow) + ')';
      ctx.shadowBlur = 60 * S.doneGlow * inv;
      ctx.fillStyle = '#000';
      ctx.fillRect(S.solX, S.solY, S.imgW, S.imgH);
      ctx.restore();
    }

    for (var i = 0; i < S.zOrder.length; i++) {
      var p = S.zOrder[i];
      var x = p.x + p.ax - S.margin, y = p.y + p.ay - S.margin;
      if (x > vx1 || y > vy1 || x + S.cw < vx0 || y + S.ch < vy0) continue;
      ctx.drawImage(S.atlas, p.sx, p.sy, S.cw, S.ch, x, y, S.cw, S.ch);
    }

    // outline assembled-but-loose clusters, and highlight the one being dragged
    S.groups.forEach(function (g) {
      if (g.anchored || g.pieces.length < 2) return;
      var dragging = drag && drag.type === 'piece' && drag.gid === g.id;
      strokeOutline(g.pieces, dragging ? 'rgba(110,168,254,.95)' : 'rgba(255,255,255,.35)',
                    (dragging ? 2.5 : 1.5) * inv);
    });
    if (drag && drag.type === 'piece') {
      var dg = S.groups.get(drag.gid);
      if (dg && dg.pieces.length === 1) strokeOutline(dg.pieces, 'rgba(110,168,254,.95)', 2.5 * inv);
    }

    ctx.restore();
  }

  var lastFrame = performance.now();
  function frame(now) {
    requestAnimationFrame(frame);
    var dt = Math.min(80, now - lastFrame);
    lastFrame = now;
    if (anim.size) {
      var k = Math.exp(-dt / 55);
      anim.forEach(function (p) {
        p.ax *= k; p.ay *= k;
        if (Math.abs(p.ax) < 0.25 && Math.abs(p.ay) < 0.25) { p.ax = 0; p.ay = 0; anim.delete(p); }
      });
      dirty = true;
    }
    if (S.doneGlow > 0) { S.doneGlow = Math.max(0, S.doneGlow - dt / 1400); dirty = true; }
    if (!dirty || el.game.hidden) return;
    dirty = false;
    draw();
  }
  requestAnimationFrame(frame);

  // timer ticks independently of the render loop
  var lastTick = performance.now();
  setInterval(function () {
    var now = performance.now(), dt = now - lastTick;
    lastTick = now;
    if (S.running && !S.complete && !document.hidden && dt < 1000) {
      S.elapsed += dt;
      el.timer.textContent = fmtTime(S.elapsed);
    }
  }, 250);

  /* ------------------------------------------------------- reference panel */

  // Kept in stage coordinates so it survives resizes and reloads.
  function placeThumb(x, y) {
    var w = el.thumb.offsetWidth || 0, h = el.thumb.offsetHeight || 0;
    x = Math.max(0, Math.min(vw - w, x));
    y = Math.max(0, Math.min(vh - h, y));
    S.thumbPos = { x: x, y: y };
    el.thumb.style.left = x + 'px';
    el.thumb.style.top = y + 'px';
    el.thumb.style.right = 'auto';
    el.thumb.style.bottom = 'auto';
  }

  function applyThumbPos() {
    if (S.thumbPos && !el.thumb.hidden) placeThumb(S.thumbPos.x, S.thumbPos.y);
  }

  var thumbDrag = null;
  el.thumbBar.addEventListener('pointerdown', function (e) {
    if (e.target === el.thumbClose) return;
    var box = el.thumb.getBoundingClientRect(), stage = el.stage.getBoundingClientRect();
    thumbDrag = { dx: e.clientX - box.left, dy: e.clientY - box.top };
    el.thumbBar.setPointerCapture(e.pointerId);
    placeThumb(box.left - stage.left, box.top - stage.top);
    e.preventDefault();
  });
  el.thumbBar.addEventListener('pointermove', function (e) {
    if (!thumbDrag) return;
    var stage = el.stage.getBoundingClientRect();
    placeThumb(e.clientX - stage.left - thumbDrag.dx, e.clientY - stage.top - thumbDrag.dy);
  });
  function endThumbDrag() { if (thumbDrag) { thumbDrag = null; save(); } }
  el.thumbBar.addEventListener('pointerup', endThumbDrag);
  el.thumbBar.addEventListener('pointercancel', endThumbDrag);

  /* ---------------------------------------------------------------- pointers */

  var drag = null;
  var pointers = new Map();
  var pinch = null;

  function localPos(e) {
    var r = el.canvas.getBoundingClientRect();
    return { x: e.clientX - r.left, y: e.clientY - r.top };
  }

  var hitCtx = document.createElement('canvas').getContext('2d');

  function pickPiece(wx, wy) {
    for (var i = S.zOrder.length - 1; i >= 0; i--) {
      var p = S.zOrder[i];
      if (p.gid === 0) continue;
      var lx = wx - p.x, ly = wy - p.y;
      if (lx < -S.margin || ly < -S.margin || lx > S.pw + S.margin || ly > S.ph + S.margin) continue;
      if (hitCtx.isPointInPath(p.path, lx, ly)) return p;
    }
    return null;
  }

  el.canvas.addEventListener('pointerdown', function (e) {
    if (!S.img) return;
    el.canvas.setPointerCapture(e.pointerId);
    pointers.set(e.pointerId, localPos(e));
    if (pointers.size === 2) {
      var pts = Array.from(pointers.values());
      pinch = {
        d: Math.hypot(pts[0].x - pts[1].x, pts[0].y - pts[1].y),
        mx: (pts[0].x + pts[1].x) / 2, my: (pts[0].y + pts[1].y) / 2,
        cam: { x: S.cam.x, y: S.cam.y, scale: S.cam.scale }
      };
      drag = null;
      return;
    }
    var pos = localPos(e);
    var w = screenToWorld(pos.x, pos.y);
    var piece = (S.running && !S.complete) ? pickPiece(w.x, w.y) : null;
    if (piece) {
      drag = { type: 'piece', gid: piece.gid, lx: w.x, ly: w.y, moved: false };
      bringToFront(groupOf(piece));
      dirty = true;
    } else {
      drag = { type: 'pan', sx: pos.x, sy: pos.y, cx: S.cam.x, cy: S.cam.y };
      el.canvas.classList.add('grabbing');
    }
  });

  el.canvas.addEventListener('pointermove', function (e) {
    if (!pointers.has(e.pointerId)) return;
    pointers.set(e.pointerId, localPos(e));

    if (pinch && pointers.size >= 2) {
      var pts = Array.from(pointers.values());
      var d = Math.hypot(pts[0].x - pts[1].x, pts[0].y - pts[1].y);
      var mx = (pts[0].x + pts[1].x) / 2, my = (pts[0].y + pts[1].y) / 2;
      var want = Math.min(maxScale(), Math.max(minScale(), pinch.cam.scale * (d / pinch.d)));
      var wx = (pinch.mx - pinch.cam.x) / pinch.cam.scale, wy = (pinch.my - pinch.cam.y) / pinch.cam.scale;
      S.cam.scale = want;
      S.cam.x = mx - wx * want;
      S.cam.y = my - wy * want;
      dirty = true;
      return;
    }
    if (!drag) return;
    var pos = localPos(e);

    if (drag.type === 'pan') {
      S.cam.x = drag.cx + (pos.x - drag.sx);
      S.cam.y = drag.cy + (pos.y - drag.sy);
      dirty = true;
      return;
    }

    var g = S.groups.get(drag.gid);
    if (!g) { drag = null; return; }
    var w = screenToWorld(pos.x, pos.y);
    var dx = w.x - drag.lx, dy = w.y - drag.ly;

    if (dx || dy) {
      translateGroup(g, dx, dy);
      drag.lx = w.x;
      drag.ly = w.y;
      drag.moved = true;
      dirty = true;
    }
  });

  function endPointer(e) {
    pointers.delete(e.pointerId);
    if (pointers.size < 2) pinch = null;
    if (!drag) { if (pointers.size === 0) save(); return; }
    var d = drag;
    drag = null;
    el.canvas.classList.remove('grabbing');
    if (d.type === 'piece' && d.moved) trySnap(d.gid);
    dirty = true;
    save();
  }
  el.canvas.addEventListener('pointerup', endPointer);
  el.canvas.addEventListener('pointercancel', endPointer);

  el.canvas.addEventListener('wheel', function (e) {
    if (!S.img) return;
    e.preventDefault();
    var pos = localPos(e);
    var unit = e.deltaMode === 1 ? 16 : e.deltaMode === 2 ? vh : 1;
    zoomAt(pos.x, pos.y, Math.exp(-e.deltaY * unit * 0.0016));
  }, { passive: false });

  el.canvas.addEventListener('contextmenu', function (e) { e.preventDefault(); });

  /* ------------------------------------------------------------- persistence */

  // localStorage holds the small state so it can still be written while the
  // page is closing. A photo too large for it goes to IndexedDB instead, which
  // has room for the full-resolution copy.
  var dbOpen = null;
  function db() {
    if (dbOpen) return dbOpen;
    dbOpen = new Promise(function (res, rej) {
      if (!window.indexedDB) { rej(new Error('no indexeddb')); return; }
      var req = indexedDB.open('jigsaw', 1);
      req.onupgradeneeded = function () { req.result.createObjectStore(PHOTO_STORE); };
      req.onsuccess = function () { res(req.result); };
      req.onerror = function () { rej(req.error || new Error('open failed')); };
      req.onblocked = function () { rej(new Error('blocked')); };
    });
    return dbOpen;
  }
  function dbRun(mode, run) {
    return db().then(function (conn) {
      return new Promise(function (res, rej) {
        var tx = conn.transaction(PHOTO_STORE, mode);
        var out = run(tx.objectStore(PHOTO_STORE), res);
        tx.onerror = function () { rej(tx.error || new Error('tx failed')); };
        tx.onabort = function () { rej(new Error('tx aborted')); };
        if (mode === 'readwrite') tx.oncomplete = function () { res(out); };
      });
    });
  }
  function dbPutPhoto(data) { return dbRun('readwrite', function (st) { st.put(data, 'photo'); }); }
  function dbDeletePhoto() { return dbRun('readwrite', function (st) { st.delete('photo'); }); }
  function dbGetPhoto() {
    return dbRun('readonly', function (st, res) {
      var req = st.get('photo');
      req.onsuccess = function () { res(req.result); };
    });
  }


  function serialize() {
    var r1 = function (n) { return Math.round(n * 10) / 10; };
    return {
      v: 1, img: S.imgInIdb ? '' : (S.saveData || S.imgData), imgIdb: S.imgInIdb,
      imgW: S.imgW, imgH: S.imgH, cols: S.cols, rows: S.rows,
      elapsed: Math.round(S.elapsed), complete: S.complete, bg: S.bg,
      sound: S.sound, thumb: S.showThumb, thumbPos: S.thumbPos,
      edges: { v: encodeSigns(S.vs), h: encodeSigns(S.hs) },
      cam: { x: r1(S.cam.x), y: r1(S.cam.y), scale: S.cam.scale },
      pieces: S.pieces.map(function (p) { return [r1(p.x), r1(p.y), p.gid]; })
    };
  }

  // The photo on screen is kept at full size; only the stored copy shrinks,
  // and only as far as it must to fit. Resuming then costs some sharpness
  // instead of failing outright.
  function shrinkSaveData() {
    S.saveScale *= 0.7;
    var w = Math.max(200, Math.round(S.imgW * S.saveScale));
    var h = Math.max(200, Math.round(S.imgH * S.saveScale));
    var c = document.createElement('canvas');
    c.width = w; c.height = h;
    var g = c.getContext('2d');
    g.imageSmoothingQuality = 'high';
    g.drawImage(S.img, 0, 0, w, h);
    S.saveData = c.toDataURL('image/jpeg', 0.82);
  }

  var saveBroken = false, dbBroken = false, photoWrite = null;

  // Move the photo to IndexedDB, then write the state again without it.
  function offloadPhoto() {
    if (photoWrite || S.imgInIdb || dbBroken) return;
    photoWrite = dbPutPhoto(S.saveData).then(function () {
      photoWrite = null;
      S.imgInIdb = true;
      saveNow();
    }).catch(function () {
      photoWrite = null;
      dbBroken = true;
      saveNow();              // fall back to shrinking the photo instead
    });
  }

  function saveNow() {
    if (!S.img || saveBroken) return;
    if (!S.imgInIdb && !dbBroken && S.saveData.length > SAVE_CHARS) { offloadPhoto(); return; }
    if (photoWrite) return;   // a write is in flight and will save when it lands
    while (!S.imgInIdb && S.saveData.length > SAVE_CHARS && S.saveScale > 0.3) shrinkSaveData();
    for (var attempt = 0; attempt < 4; attempt++) {
      try {
        localStorage.setItem(SAVE_KEY, JSON.stringify(serialize()));
        return;
      } catch (err) {
        if (!S.imgInIdb && !dbBroken) { offloadPhoto(); return; }
        if (S.saveScale <= 0.3) break;
        shrinkSaveData();
      }
    }
    saveBroken = true;
    toast('Auto-save unavailable: browser storage is full.');
  }
  function save() {
    clearTimeout(saveTimer);
    saveTimer = setTimeout(saveNow, 700);
  }

  function restore(d, img, src) {
    S.img = img;
    S.imgData = src;
    S.saveData = src;
    S.imgInIdb = !!d.imgIdb;
    S.saveScale = img.naturalWidth && d.imgW ? img.naturalWidth / d.imgW : 1;
    S.imgW = d.imgW; S.imgH = d.imgH;
    S.cols = d.cols; S.rows = d.rows;
    buildPieces(d.edges);
    S.groups = new Map();
    S.groups.set(0, { id: 0, anchored: true, pieces: [] });
    var maxGid = 0;
    for (var i = 0; i < S.pieces.length; i++) {
      var p = S.pieces[i], rec = d.pieces[i];
      p.x = rec[0]; p.y = rec[1]; p.gid = rec[2];
      if (p.gid > maxGid) maxGid = p.gid;
      var g = S.groups.get(p.gid);
      if (!g) { g = { id: p.gid, anchored: p.gid === 0, pieces: [] }; S.groups.set(p.gid, g); }
      g.pieces.push(p);
    }
    S.nextGid = maxGid + 1;
    S.placed = S.groups.get(0).pieces.length;
    sendToBack(S.groups.get(0).pieces);
    S.elapsed = d.elapsed || 0;
    S.complete = !!d.complete;
    S.running = false;                       // resume paused, player presses play
    S.bg = d.bg || S.bg;
    S.sound = d.sound !== false;
    S.showThumb = d.thumb !== false;
    S.thumbPos = d.thumbPos || null;
    el.thumbImg.src = S.imgData;
    show('game');
    if (d.cam && d.cam.scale) { S.cam.x = d.cam.x; S.cam.y = d.cam.y; S.cam.scale = d.cam.scale; }
    else fitView();
    if (S.complete) {
      el.finalTime.textContent = fmtTime(S.elapsed);
      el.finalPieces.textContent = String(S.pieces.length);
      el.done.hidden = false;
    }
    syncChrome();
    updateHud();
    dirty = true;
    if (!S.complete) toast('Resumed your saved puzzle — press play to continue.');
  }

  function inProgress() { return !!S.img && !S.complete && S.placed < S.pieces.length; }

  function newPuzzle() {
    if (inProgress() && !confirm('Start a new puzzle? Your current progress will be lost.')) return;
    try { localStorage.removeItem(SAVE_KEY); } catch (e) { /* ignore */ }
    if (S.imgInIdb) dbDeletePhoto().catch(function () { /* nothing to clean up */ });
    S.imgInIdb = false;
    clearTimeout(saveTimer);
    S.img = null; S.imgData = ''; S.pieces = []; S.zOrder = [];
    S.groups = new Map(); S.placed = 0; S.elapsed = 0;
    S.running = false; S.complete = false;
    el.done.hidden = true;
    el.btnSummary.hidden = true;
    el.file.value = '';
    show('upload');
  }

  /* ------------------------------------------------------------------- wiring */

  el.file.addEventListener('change', function () { if (el.file.files[0]) handleFile(el.file.files[0]); });
  ['dragenter', 'dragover'].forEach(function (t) {
    el.upload.addEventListener(t, function (e) { e.preventDefault(); el.drop.classList.add('over'); });
  });
  ['dragleave', 'drop'].forEach(function (t) {
    el.upload.addEventListener(t, function (e) { e.preventDefault(); el.drop.classList.remove('over'); });
  });
  el.upload.addEventListener('drop', function (e) {
    if (e.dataTransfer && e.dataTransfer.files[0]) handleFile(e.dataTransfer.files[0]);
  });

  el.setupBack.addEventListener('click', function () { pending = null; el.file.value = ''; show('upload'); });
  el.setupStart.addEventListener('click', function () { if (pending) startPuzzle(pendingTarget); });

  el.btnNew.addEventListener('click', newPuzzle);
  el.btnDoneNew.addEventListener('click', newPuzzle);
  el.btnAdmire.addEventListener('click', function () { el.done.hidden = true; el.btnSummary.hidden = false; });
  el.btnSummary.addEventListener('click', function () { el.done.hidden = false; el.btnSummary.hidden = true; });

  el.pause.addEventListener('click', function () {
    if (S.complete || !S.img) return;
    S.running = !S.running;
    syncChrome();
    save();
  });
  el.veil.addEventListener('click', function () {
    if (S.complete || !S.img) return;
    S.running = true;
    syncChrome();
  });

  el.btnThumb.addEventListener('click', function () { S.showThumb = !S.showThumb; syncChrome(); save(); });
  el.thumbClose.addEventListener('click', function () { S.showThumb = false; syncChrome(); save(); });
  el.btnSound.addEventListener('click', function () { S.sound = !S.sound; syncChrome(); save(); });

  BACKGROUNDS.forEach(function (b) {
    var o = document.createElement('option');
    o.value = b.id; o.textContent = b.name;
    el.bgSelect.appendChild(o);
  });
  el.bgSelect.addEventListener('change', function () { S.bg = el.bgSelect.value; dirty = true; save(); });

  el.zoomIn.addEventListener('click', function () { zoomAt(vw / 2, vh / 2, 1.25); });
  el.zoomOut.addEventListener('click', function () { zoomAt(vw / 2, vh / 2, 0.8); });
  el.fit.addEventListener('click', function () { fitView(); save(); });

  document.addEventListener('keydown', function (e) {
    if (el.game.hidden || e.metaKey || e.ctrlKey || e.altKey) return;
    var k = e.key.toLowerCase();
    if (k === 'p') el.pause.click();
    else if (k === 'h') el.btnThumb.click();
    else if (k === 'f') el.fit.click();
    else if (k === '+' || k === '=') el.zoomIn.click();
    else if (k === '-') el.zoomOut.click();
  });

  window.addEventListener('resize', resize);
  window.addEventListener('beforeunload', function () { clearTimeout(saveTimer); saveNow(); });
  document.addEventListener('visibilitychange', function () { if (document.hidden) saveNow(); });

  /* --------------------------------------------------------------------- boot */

  (function boot() {
    syncChrome();
    resize();
    var raw = null;
    try { raw = localStorage.getItem(SAVE_KEY); } catch (e) { raw = null; }
    if (!raw) { show('upload'); return; }
    var data;
    try { data = JSON.parse(raw); } catch (e) { show('upload'); return; }
    var sane = data && data.v === 1 && (data.img || data.imgIdb) && Array.isArray(data.pieces) &&
               data.cols > 0 && data.rows > 0 && data.pieces.length === data.cols * data.rows;
    if (!sane) { show('upload'); return; }
    var photo = data.imgIdb ? dbGetPhoto() : Promise.resolve(data.img);
    photo.then(function (src) {
      if (!src) throw new Error('photo missing');
      return loadImage(src).then(function (img) {
        resize();
        restore(data, img, src);
      });
    }).catch(function () { show('upload'); });
  })();
})();
