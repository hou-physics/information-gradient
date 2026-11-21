/* home.js: the book's root model, live, on the home page (book/site/build_site.py writes the page).

   A crowd of grey dots on a quiet field, each person joined to a few neighbours in a loose network that is not drawn.
   A few people hear the news at the start. After that, each person who has not heard it hears it from an outside
   source (the press, a filing) at a small rate, and from each neighbour who already knows at a larger rate: the root
   model's external rate alpha and word-of-mouth rate beta (Chapter 1, Section 1.5; Chapter 5), with a person's
   neighbours in place of the whole crowd. A dot turns ink blue when its person hears. News passed by word of mouth
   leaves a thin blue line from teller to hearer, so the paths the news took grow into trees; a thin ring marks news
   from the outside source. The informed fraction rises slowly, then fast, then slowly, and the corner draws it as it
   goes. When nearly everyone has heard, the field rests, fades back and starts again from new seeds.

   Cost: at most 30 frames a second, and nothing runs while the tab is hidden or the field is off screen. With
   prefers-reduced-motion the page shows one still frame, a run stopped halfway. The canvas has up to 2 pixels per
   CSS pixel, so it stays sharp on high-density screens. The colours are style.css's --field-* and --line, read
   again when the reader's light or dark setting changes. Elements marked data-clear keep the dots away from them.
   No library. */
(() => {
  "use strict";

  const stage = document.querySelector(".hero-stage");
  const field = stage && stage.querySelector(".hero-field");
  const ctx = field && field.getContext("2d");
  if (!ctx) return;
  const curve = stage.querySelector(".hero-curve");
  const cctx = curve && curve.getContext("2d");
  const share = stage.querySelector(".hero-share");

  // The crowd (lengths in CSS pixels)
  const SPACING = [24, 20];  // grid step, wide and narrow screens; each dot sits somewhere in its cell
  const KEEP = 0.8;          // share of cells that hold a dot
  const LINK = 0.8;          // chance of a link to the neighbour on the right and the one below
  const DIAGONAL = 0.35;     // chance of a link to each lower diagonal neighbour
  const REACH = 3;           // a group of dots left apart is joined to the nearest dot within this many steps
  const CLEAR = 16;          // room kept free around text
  const SOFT = 40;           // dots this close to text or to the top and bottom edges are drawn fainter
  // The model (rates per second of animation)
  const TELL = 1.2;          // word of mouth, per neighbour who knows
  const HEAR = 0.0025;       // the outside source, per person
  const SEED_EVERY = 600;    // one person in this many hears at the start (at least two)
  const DONE = 0.97;         // the run ends when this share has heard
  const LONGEST = 25;        // or after this many seconds
  // The look (seconds)
  const HOLD = 2.5, FADE = 1.6, TURN = 0.4, FLASH = 0.9, RING = 1.1;
  const STEPS = 5;           // colour steps between grey and blue
  const R_OFF = 1.5, R_ON = 2.3;
  const SPAN = 14;           // seconds the S-curve's width shows, at least
  const FPS = 30;
  const LAYOUT_SEED = 20261121;

  const reduce = matchMedia("(prefers-reduced-motion: reduce)");
  const scheme = matchMedia("(prefers-color-scheme: dark)");

  let W = 0, H = 0, dpr = 1;
  let n = 0, xs = [], ys = [], level = new Uint8Array(0), first = new Int32Array(1), adj = new Int32Array(0);
  let edgeA = [], edgeB = [];
  let heard = new Uint8Array(0), since = new Float32Array(0), kinf = new Uint16Array(0), step = new Uint8Array(0);
  let colors = null, rand = Math.random;
  let t = 0, phase = "run", phaseT = 0, count = 0, history = [], paths = [], flashes = [], rings = [];
  let raf = 0, last = 0, inView = true, shown = "", pending = 0, layout = "";

  function seeded(a) {  // mulberry32
    return () => {
      a = (a + 0x6d2b79f5) | 0;
      let x = Math.imul(a ^ (a >>> 15), 1 | a);
      x = (x + Math.imul(x ^ (x >>> 7), 61 | x)) ^ x;
      return ((x ^ (x >>> 14)) >>> 0) / 4294967296;
    };
  }

  function readColors() {
    const probe = document.createElement("span");
    probe.style.display = "none";
    stage.appendChild(probe);
    const get = (name) => {
      probe.style.color = `var(${name})`;
      const v = (getComputedStyle(probe).color.match(/[\d.]+/g) || []).map(Number);
      return [v[0] || 0, v[1] || 0, v[2] || 0, v.length > 3 ? v[3] : 1];
    };
    const css = (c) => `rgba(${c.slice(0, 3).map(Math.round).join(",")},${c[3]})`;
    const off = get("--field-dot"), on = get("--field-on");
    colors = { link: css(get("--field-link")), on: css(on),
               line: css(get("--line")), steps: [] };
    for (let s = 0; s <= STEPS; s++) colors.steps.push(css(off.map((v, k) => v + (on[k] - v) * s / STEPS)));
    probe.remove();
  }

  // The crowd: dots on a jittered grid, outside the text; links between grid neighbours.
  function build() {
    const box = stage.getBoundingClientRect();
    W = Math.round(box.width);
    H = Math.round(box.height);
    if (!W || !H) return false;
    dpr = Math.min(window.devicePixelRatio || 1, 2);
    field.width = Math.round(W * dpr);
    field.height = Math.round(H * dpr);
    if (cctx) {
      curve.width = Math.round(curve.clientWidth * dpr);
      curve.height = Math.round(curve.clientHeight * dpr);
    }
    const clear = [];
    for (const el of stage.querySelectorAll("[data-clear]")) {
      const r = el.getBoundingClientRect();
      if (r.width && r.height) clear.push([r.left - box.left, r.top - box.top, r.right - box.left, r.bottom - box.top]);
    }
    const gap = (x, y) => {
      let d = Infinity;
      for (const [l, tp, r, b] of clear) {
        d = Math.min(d, Math.hypot(Math.max(l - x, 0, x - r), Math.max(tp - y, 0, y - b)));
      }
      return d;
    };
    const g = seeded(LAYOUT_SEED);
    const S = SPACING[W < 640 ? 1 : 0];
    const cols = Math.ceil(W / S) + 1, rows = Math.ceil(H / S) + 1;
    const ox = (cols * S - W) / 2, oy = (rows * S - H) / 2;
    const cell = new Int32Array(cols * rows).fill(-1);
    const levels = [];
    xs = []; ys = [];
    for (let r = 0; r < rows; r++) {
      for (let c = 0; c < cols; c++) {
        const keep = g() < KEEP, x = (c + 0.15 + 0.7 * g()) * S - ox, y = (r + 0.15 + 0.7 * g()) * S - oy;
        if (!keep || x < 3 || x > W - 3 || y < 3 || y > H - 3) continue;
        const d = gap(x, y) - CLEAR;
        if (d < 0) continue;
        const near = Math.min(d, y, H - y);
        cell[r * cols + c] = xs.length;
        xs.push(x); ys.push(y);
        levels.push(near < SOFT / 2 ? 2 : near < SOFT ? 1 : 0);
      }
    }
    n = xs.length;
    level = Uint8Array.from(levels);
    edgeA = []; edgeB = [];
    const degree = new Int32Array(n);
    for (let r = 0; r < rows; r++) {
      for (let c = 0; c < cols; c++) {
        const i = cell[r * cols + c];
        if (i < 0) continue;
        for (const [dc, dr, p] of [[1, 0, LINK], [0, 1, LINK], [1, 1, DIAGONAL], [-1, 1, DIAGONAL]]) {
          const cc = c + dc, rr = r + dr;
          if (cc < 0 || cc >= cols || rr >= rows || g() >= p) continue;
          const j = cell[rr * cols + cc];
          if (j < 0 || gap((xs[i] + xs[j]) / 2, (ys[i] + ys[j]) / 2) < CLEAR * 0.75) continue;
          edgeA.push(i); edgeB.push(j);
          degree[i]++; degree[j]++;
        }
      }
    }
    // Join each group of dots that no link reaches to the nearest dot outside it, so the news can reach everyone
    const group = Int32Array.from({ length: n }, (_, i) => i);
    const find = (i) => {
      while (group[i] !== i) i = group[i] = group[group[i]];
      return i;
    };
    for (let e = 0; e < edgeA.length; e++) group[find(edgeA[e])] = find(edgeB[e]);
    const members = new Map();
    for (let i = 0; i < n; i++) {
      const r = find(i);
      if (!members.has(r)) members.set(r, []);
      members.get(r).push(i);
    }
    const groups = [...members.values()].sort((a, b) => a.length - b.length);
    for (const g0 of groups.slice(0, -1)) {
      const own = find(g0[0]);
      let best = REACH * S, bi = -1, bj = -1;
      for (const i of g0) {
        for (let j = 0; j < n; j++) {
          const d = Math.hypot(xs[i] - xs[j], ys[i] - ys[j]);
          if (d < best && find(j) !== own && gap((xs[i] + xs[j]) / 2, (ys[i] + ys[j]) / 2) >= CLEAR * 0.75) {
            best = d; bi = i; bj = j;
          }
        }
      }
      if (bi < 0) continue;
      edgeA.push(bi); edgeB.push(bj);
      degree[bi]++; degree[bj]++;
      group[own] = find(bj);
    }
    first = new Int32Array(n + 1);
    for (let i = 0; i < n; i++) first[i + 1] = first[i] + degree[i];
    adj = new Int32Array(first[n]);
    const fill = first.slice(0, n);
    for (let e = 0; e < edgeA.length; e++) {
      adj[fill[edgeA[e]]++] = edgeB[e];
      adj[fill[edgeB[e]]++] = edgeA[e];
    }
    step = new Uint8Array(n);
    return n > 0;
  }

  // The model
  function inform(i, from) {
    heard[i] = 1;
    since[i] = t;
    count++;
    for (let k = first[i]; k < first[i + 1]; k++) kinf[adj[k]]++;
    if (from >= 0) {
      paths.push(from, i);
      flashes.push([from, i, t]);
    } else {
      rings.push([i, t]);
    }
  }

  function teller(i) {  // one of the neighbours who know, at random
    let k = Math.floor(rand() * kinf[i]);
    for (let a = first[i]; a < first[i + 1]; a++) if (heard[adj[a]] && k-- === 0) return adj[a];
    return -1;
  }

  function reset(seed) {
    rand = seed === undefined ? Math.random : seeded(seed);
    heard = new Uint8Array(n); since = new Float32Array(n); kinf = new Uint16Array(n);
    t = 0; phase = "run"; phaseT = 0; count = 0; paths = []; flashes = []; rings = [];
    const seeds = Math.max(2, Math.round(n / SEED_EVERY));
    for (let tries = 0; count < seeds && tries < 200; tries++) {
      const i = Math.floor(rand() * n);
      if (!heard[i] && first[i + 1] - first[i] >= 2) inform(i, -1);
    }
    history = [[0, count / n]];
  }

  function advance(dt) {
    t += dt;
    phaseT += dt;
    if (phase === "run") {
      const fresh = [];
      for (let i = 0; i < n; i++) {
        if (heard[i]) continue;
        const word = TELL * kinf[i], rate = HEAR + word;
        if (rand() < 1 - Math.exp(-rate * dt)) fresh.push(i, rand() * rate < word ? teller(i) : -1);
      }
      for (let k = 0; k < fresh.length; k += 2) inform(fresh[k], fresh[k + 1]);
      history.push([t, count / n]);
      if (count / n >= DONE || t > LONGEST) { phase = "hold"; phaseT = 0; }
    } else if (phase === "hold" && phaseT >= HOLD) {
      phase = "fade"; phaseT = 0;
    } else if (phase === "fade" && phaseT >= FADE) {
      reset();
    }
    if (flashes.length && t - flashes[0][2] >= FLASH) flashes = flashes.filter((f) => t - f[2] < FLASH);
    if (rings.length && t - rings[0][1] >= RING) rings = rings.filter((r) => t - r[1] < RING);
  }

  // Drawing
  function draw() {
    const c = ctx, back = phase === "fade" ? Math.min(phaseT / FADE, 1) : 0;
    c.setTransform(dpr, 0, 0, dpr, 0, 0);
    c.clearRect(0, 0, W, H);
    c.lineWidth = 1;
    c.globalAlpha = 1 - back;
    c.strokeStyle = colors.link;
    c.beginPath();
    for (let k = 0; k < paths.length; k += 2) {
      c.moveTo(xs[paths[k]], ys[paths[k]]);
      c.lineTo(xs[paths[k + 1]], ys[paths[k + 1]]);
    }
    c.stroke();
    c.strokeStyle = colors.on;
    c.lineWidth = 1.25;
    for (const [a, b, t0] of flashes) {
      c.globalAlpha = 0.9 * (1 - (t - t0) / FLASH) * (1 - back);
      c.beginPath(); c.moveTo(xs[a], ys[a]); c.lineTo(xs[b], ys[b]); c.stroke();
    }
    for (let i = 0; i < n; i++) {
      const s = heard[i] ? Math.min(STEPS, Math.floor((t - since[i]) / TURN * STEPS)) : 0;
      step[i] = Math.round(s * (1 - back));
    }
    for (let l = 0; l < 3; l++) {
      c.globalAlpha = [1, 0.55, 0.25][l];
      for (let s = 0; s <= STEPS; s++) {
        const r = R_OFF + (R_ON - R_OFF) * s / STEPS;
        let any = false;
        c.beginPath();
        for (let i = 0; i < n; i++) {
          if (level[i] !== l || step[i] !== s) continue;
          c.moveTo(xs[i] + r, ys[i]); c.arc(xs[i], ys[i], r, 0, 2 * Math.PI); any = true;
        }
        if (any) { c.fillStyle = colors.steps[s]; c.fill(); }
      }
    }
    c.strokeStyle = colors.on;
    c.lineWidth = 1;
    for (const [i, t0] of rings) {
      const f = (t - t0) / RING;
      c.globalAlpha = 0.6 * (1 - f) * [1, 0.55, 0.25][level[i]];
      c.beginPath(); c.arc(xs[i], ys[i], R_ON + 9 * (1 - (1 - f) * (1 - f)), 0, 2 * Math.PI); c.stroke();
    }
    c.globalAlpha = 1;
  }

  function drawCurve() {
    if (!cctx || !curve.width) return;
    const c = cctx, w = curve.width / dpr, h = curve.height / dpr, top = 3, bottom = h - 3;
    const span = Math.max(SPAN, history[history.length - 1][0]);
    const x = (time) => 3 + (w - 6) * time / span, y = (share) => bottom - (bottom - top) * share;
    c.setTransform(dpr, 0, 0, dpr, 0, 0);
    c.clearRect(0, 0, w, h);
    c.globalAlpha = 1;
    c.lineWidth = 1;
    c.strokeStyle = colors.line;
    c.beginPath(); c.moveTo(0, Math.round(bottom) + 0.5); c.lineTo(w, Math.round(bottom) + 0.5); c.stroke();
    c.setLineDash([2, 3]);
    c.beginPath(); c.moveTo(0, Math.round(top) + 0.5); c.lineTo(w, Math.round(top) + 0.5); c.stroke();
    c.setLineDash([]);
    c.globalAlpha = phase === "fade" ? 1 - Math.min(phaseT / FADE, 1) : 1;
    c.strokeStyle = colors.on;
    c.lineWidth = 1.5;
    c.lineJoin = "round";
    c.beginPath();
    history.forEach(([time, s], k) => (k ? c.lineTo(x(time), y(s)) : c.moveTo(x(time), y(s))));
    c.stroke();
    const [tn, sn] = history[history.length - 1];
    c.fillStyle = colors.on;
    c.beginPath(); c.arc(x(tn), y(sn), 2.5, 0, 2 * Math.PI); c.fill();
    c.globalAlpha = 1;
  }

  function showShare() {
    if (!share) return;
    const text = `${Math.round(100 * history[history.length - 1][1])}%`;
    if (text !== shown) share.textContent = shown = text;
  }

  // Running
  function frame(now) {
    raf = requestAnimationFrame(frame);
    if (now - last < 1000 / FPS - 1) return;
    const dt = Math.min((now - last) / 1000, 0.1);
    last = now;
    advance(dt);
    if (phase !== "hold" || phaseT < Math.max(FLASH, RING, TURN) + 0.1) {
      draw();
      drawCurve();
    }
    showShare();
  }

  function update() {
    const run = n > 0 && !reduce.matches && !document.hidden && inView;
    if (run && !raf) {
      last = performance.now();
      raf = requestAnimationFrame(frame);
    } else if (!run && raf) {
      cancelAnimationFrame(raf);
      raf = 0;
    }
  }

  function still() {  // a run stopped halfway, for readers who ask for less motion
    reset(7);
    for (let k = 0; count / n < 0.5 && k < LONGEST * FPS; k++) advance(1 / FPS);
    flashes = []; rings = [];
    t += TURN;
  }

  function where() {  // the field's size and where the text sits in it
    const box = stage.getBoundingClientRect(), out = [box.width, box.height];
    for (const el of stage.querySelectorAll("[data-clear]")) {
      const r = el.getBoundingClientRect();
      out.push(r.left - box.left, r.top - box.top, r.width, r.height);
    }
    return out.map(Math.round).join(",");
  }

  function rebuild(force) {
    pending = 0;
    if (force !== true && where() === layout) return;  // a resize or font load that moved nothing
    if (raf) { cancelAnimationFrame(raf); raf = 0; }
    if (!colors) readColors();
    layout = where();
    if (!build()) return;
    if (reduce.matches) still();
    else reset();
    draw();
    drawCurve();
    showShare();
    stage.classList.add("is-live");
    update();
  }

  function later() {
    clearTimeout(pending);
    pending = setTimeout(rebuild, 150);
  }

  rebuild(true);
  new ResizeObserver(later).observe(stage);
  if (document.fonts && document.fonts.ready) document.fonts.ready.then(later);
  new IntersectionObserver((entries) => {
    inView = entries[entries.length - 1].isIntersecting;
    update();
  }).observe(stage);
  document.addEventListener("visibilitychange", update);
  reduce.addEventListener("change", () => rebuild(true));
  scheme.addEventListener("change", () => {
    readColors();
    draw();
    drawCurve();
  });
})();
