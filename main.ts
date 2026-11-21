import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const INPUT = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTPUT = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const DIRS = [
  [-1, 0, 'u'],
  [1, 0, 'd'],
  [0, -1, 'l'],
  [0, 1, 'r'],
];
const SEARCH_LIMIT = 250_000;

function parseLevel(text) {
  const rows = text.split(/\r?\n/).filter((row) => row.length > 0);
  if (rows.length === 0) throw new Error('empty level');
  const h = rows.length;
  const w = Math.max(...rows.map((row) => row.length));
  const size = w * h;
  const wall = new Uint8Array(size).fill(1);
  const goals = [];
  const boxes = [];
  let player = -1;

  for (let y = 0; y < h; y++) {
    const row = rows[y];
    for (let x = 0; x < row.length; x++) {
      const ch = row[x];
      if (ch === '#') continue;
      const p = y * w + x;
      wall[p] = 0;
      if (ch === '.' || ch === '*' || ch === '+') goals.push(p);
      if (ch === '$' || ch === '*') boxes.push(p);
      if (ch === '@' || ch === '+') player = p;
    }
  }

  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      if (x === 0 || y === 0 || x === w - 1 || y === h - 1) wall[y * w + x] = 1;
    }
  }
  if (player < 0 || boxes.length !== goals.length) throw new Error('malformed Sokoban level');
  boxes.sort((a, b) => a - b);
  return { w, h, wall, goals, boxes, player };
}

function reversePushReachability(level) {
  const { w, wall, goals } = level;
  const live = new Uint8Array(wall.length);
  const queue = [];
  for (const goal of goals) {
    if (!live[goal]) {
      live[goal] = 1;
      queue.push(goal);
    }
  }

  for (let head = 0; head < queue.length; head++) {
    const at = queue[head];
    for (const [dy, dx] of DIRS) {
      const delta = dy * w + dx;
      const box = at - delta;
      const stand = box - delta;
      if (box < 0 || box >= wall.length || stand < 0 || stand >= wall.length) continue;
      if (wall[box] || wall[stand] || live[box]) continue;
      live[box] = 1;
      queue.push(box);
    }
  }
  return live;
}

function reachableRegion(level, occupied, start, seen, stamp, stack) {
  const { w, wall } = level;
  let low = start;
  let n = 0;
  stack[n++] = start;
  seen[start] = stamp;

  while (n > 0) {
    const p = stack[--n];
    if (p < low) low = p;
    for (const [dy, dx] of DIRS) {
      const q = p + dy * w + dx;
      if (q < 0 || q >= wall.length || wall[q] || occupied[q] || seen[q] === stamp) continue;
      seen[q] = stamp;
      stack[n++] = q;
    }
  }
  return low;
}

function frozenTwoByTwo(level, occupied, goal, movedBox) {
  const { w, wall } = level;
  for (let corner = 0; corner < 4; corner++) {
    const a = movedBox - (corner & 1) - ((corner >> 1) * w);
    const b = a + 1;
    const c = a + w;
    const d = c + 1;
    if (a < 0 || d >= wall.length) continue;
    if (!(wall[a] || occupied[a]) || !(wall[b] || occupied[b]) ||
        !(wall[c] || occupied[c]) || !(wall[d] || occupied[d])) continue;
    if ((occupied[a] && !goal[a]) || (occupied[b] && !goal[b]) ||
        (occupied[c] && !goal[c]) || (occupied[d] && !goal[d])) return true;
  }
  return false;
}

function stateKey(boxes, reachableLow) {
  return String(reachableLow) + ':' + boxes.join(',');
}

function shortestWalk(level, occupied, from, to) {
  if (from === to) return '';
  const { w, wall } = level;
  const previous = new Int32Array(wall.length).fill(-1);
  const how = new Int8Array(wall.length);
  const queue = new Int32Array(wall.length);
  let head = 0;
  let tail = 0;
  queue[tail++] = from;
  previous[from] = from;

  while (head < tail && previous[to] < 0) {
    const p = queue[head++];
    for (let k = 0; k < DIRS.length; k++) {
      const [dy, dx] = DIRS[k];
      const q = p + dy * w + dx;
      if (q < 0 || q >= wall.length || wall[q] || occupied[q] || previous[q] >= 0) continue;
      previous[q] = p;
      how[q] = k;
      queue[tail++] = q;
    }
  }
  if (previous[to] < 0) throw new Error('push square is unreachable');

  const path = [];
  for (let p = to; p !== from; p = previous[p]) path.push(DIRS[how[p]][2]);
  path.reverse();
  return path.join('');
}

function solvePushOptimal(level) {
  const { w, wall, goals, boxes: initialBoxes, player } = level;
  const size = wall.length;
  const goal = new Uint8Array(size);
  for (const p of goals) goal[p] = 1;
  const live = reversePushReachability(level);
  if (initialBoxes.some((p) => !live[p])) return null;

  const occupied = new Uint8Array(size);
  const seen = new Int32Array(size);
  const marked = new Int32Array(size);
  const stack = new Int32Array(size);
  let stamp = 0;

  const boxes0 = initialBoxes.slice();
  const statesBoxes = [boxes0];
  const statesPlayer = [player];
  const parents = [-1];
  const pushedFrom = [-1];
  const pushedTo = [-1];
  const visited = new Map();
  for (const p of boxes0) occupied[p] = 1;
  const firstLow = reachableRegion(level, occupied, player, seen, ++stamp, stack);
  visited.set(stateKey(boxes0, firstLow), 0);
  for (const p of boxes0) occupied[p] = 0;

  if (boxes0.every((p) => goal[p])) return '';
  let found = -1;

  for (let head = 0; head < statesBoxes.length && found < 0; head++) {
    const boxes = statesBoxes[head];
    for (const p of boxes) occupied[p] = 1;
    const regionStamp = ++stamp;
    reachableRegion(level, occupied, statesPlayer[head], seen, regionStamp, stack);

    for (let bi = 0; bi < boxes.length && found < 0; bi++) {
      const from = boxes[bi];
      for (const [dy, dx, letter] of DIRS) {
        const delta = dy * w + dx;
        if (seen[from - delta] !== regionStamp) continue;
        const to = from + delta;
        if (to < 0 || to >= size || wall[to] || occupied[to] || !live[to]) continue;

        occupied[from] = 0;
        occupied[to] = 1;
        const frozen = frozenTwoByTwo(level, occupied, goal, to);
        let next = null;
        let nextKey = '';
        if (!frozen) {
          next = boxes.slice();
          next[bi] = to;
          next.sort((a, b) => a - b);
          const nextLow = reachableRegion(level, occupied, from, marked, ++stamp, stack);
          nextKey = stateKey(next, nextLow);
        }
        occupied[to] = 0;
        occupied[from] = 1;
        if (frozen || visited.has(nextKey)) continue;

        if (statesBoxes.length >= SEARCH_LIMIT) {
          for (const p of boxes) occupied[p] = 0;
          return null;
        }
        const index = statesBoxes.length;
        visited.set(nextKey, index);
        statesBoxes.push(next);
        statesPlayer.push(from);
        parents.push(head);
        pushedFrom.push(from);
        pushedTo.push(to);
        if (next.every((p) => goal[p])) {
          found = index;
          break;
        }
      }
    }
    for (const p of boxes) occupied[p] = 0;
  }

  if (found < 0) return null;
  const path = [];
  for (let state = found; state > 0; state = parents[state]) path.push(state);
  path.reverse();

  let moves = '';
  let currentPlayer = player;
  let currentBoxes = boxes0;
  for (const state of path) {
    const from = pushedFrom[state];
    const to = pushedTo[state];
    const delta = to - from;
    const stand = from - delta;
    for (const p of currentBoxes) occupied[p] = 1;
    moves += shortestWalk(level, occupied, currentPlayer, stand);
    for (const p of currentBoxes) occupied[p] = 0;
    const direction = DIRS.find(([dy, dx]) => dy * w + dx === delta);
    moves += direction[2].toUpperCase();
    currentPlayer = from;
    currentBoxes = statesBoxes[state];
  }
  return moves;
}

function findRooms(level) {
  const { w, wall, goals, boxes, player } = level;
  const live = reversePushReachability(level);
  const hallwayRow = Math.floor(player / w);
  const cut = new Uint8Array(wall.length);
  for (let p = hallwayRow * w; p < (hallwayRow + 1) * w; p++) {
    if (!wall[p] && !live[p]) cut[p] = 1;
  }
  if (boxes.some((p) => cut[p])) return null;

  const part = new Int32Array(wall.length).fill(-1);
  const rooms = [];
  for (let start = 0; start < wall.length; start++) {
    if (wall[start] || cut[start] || part[start] >= 0) continue;
    const cells = [start];
    part[start] = rooms.length;
    for (let i = 0; i < cells.length; i++) {
      const p = cells[i];
      for (const [dy, dx] of DIRS) {
        const q = p + dy * w + dx;
        if (q < 0 || q >= wall.length || wall[q] || cut[q] || part[q] >= 0) continue;
        part[q] = rooms.length;
        cells.push(q);
      }
    }
    rooms.push({ cells, boxes: [], goals: [], done: false });
  }

  for (const p of boxes) {
    if (part[p] < 0) return null;
    rooms[part[p]].boxes.push(p);
  }
  for (const p of goals) {
    if (part[p] < 0) return null;
    rooms[part[p]].goals.push(p);
  }
  if (rooms.some((room) => room.boxes.length !== room.goals.length)) return null;
  return rooms.filter((room) => room.boxes.length > 0);
}

function endPosition(w, start, moves) {
  let p = start;
  for (const ch of moves.toLowerCase()) {
    if (ch === 'u') p -= w;
    else if (ch === 'd') p += w;
    else if (ch === 'l') p--;
    else p++;
  }
  return p;
}

function solveLevel(level) {
  const rooms = findRooms(level);
  if (!rooms || rooms.length === 0) return null;
  let player = level.player;
  let solution = '';

  for (const room of rooms) {
    const wall = level.wall.slice();
    for (const other of rooms) {
      if (other === room) continue;
      for (const p of other.done ? other.goals : other.boxes) wall[p] = 1;
    }
    const sublevel = {
      w: level.w,
      h: level.h,
      wall,
      goals: room.goals.slice().sort((a, b) => a - b),
      boxes: room.boxes.slice().sort((a, b) => a - b),
      player,
    };
    const moves = solvePushOptimal(sublevel);
    if (moves === null) return null;
    solution += moves;
    player = endPosition(level.w, player, moves);
    room.done = true;
  }
  return solution;
}

for (const id of readdirSync(INPUT, { withFileTypes: true })
  .filter((entry) => entry.isDirectory())
  .map((entry) => entry.name)
  .sort()) {
  const level = parseLevel(readFileSync(join(INPUT, id, 'level.txt'), 'utf8'));
  const solution = solveLevel(level);
  if (solution === null) throw new Error('could not solve ' + id + ' within the search limit');
  mkdirSync(join(OUTPUT, id), { recursive: true });
  writeFileSync(join(OUTPUT, id, 'solution.txt'), solution + '\n');
}