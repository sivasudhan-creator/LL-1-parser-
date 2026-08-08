class GrammarEngine {
  constructor() {
    this.rules = new Map();
    this.nonTerminals = [];
    this.terminals = new Set();
    this.startSymbol = null;
    this.firstSets = new Map();
    this.followSets = new Map();
    this.parsingTable = new Map();
    this.hasConflicts = false;
  }

  parseInput(text) {
    this.rules.clear();
    this.nonTerminals = [];
    this.terminals.clear();
    this.startSymbol = null;

    const lines = text.split('\n').filter(l => l.trim().length > 0);
    lines.forEach((line, idx) => {
      const parts = line.split('->');
      if (parts.length !== 2) return;
      const head = parts[0].trim();
      const alternatives = parts[1].split('|').map(alt => alt.trim().split(/\s+/).filter(Boolean));

      if (idx === 0) this.startSymbol = head;
      if (!this.rules.has(head)) {
        this.rules.set(head, []);
        this.nonTerminals.push(head);
      }
      alternatives.forEach(alt => this.rules.get(head).push(alt));
    });

    this.rules.forEach((prods) => {
      prods.forEach(prod => {
        prod.forEach(symbol => {
          if (!this.rules.has(symbol) && symbol !== 'e' && symbol !== 'ε') {
            this.terminals.add(symbol);
          }
        });
      });
    });
    this.terminals.add('$');
  }

  eliminateLeftRecursion() {
    const newRules = new Map();
    const newNonTerminals = [];

    this.nonTerminals.forEach(A => {
      const prods = this.rules.get(A) || [];
      const recursive = [];
      const nonRecursive = [];

      prods.forEach(prod => {
        if (prod[0] === A) recursive.push(prod.slice(1));
        else nonRecursive.push(prod);
      });

      if (recursive.length > 0) {
        const A_prime = A + "'";
        newNonTerminals.push(A, A_prime);
        const newAProds = nonRecursive.map(beta => [...beta, A_prime]);
        const newAPrimeProds = recursive.map(alpha => [...alpha, A_prime]);
        newAPrimeProds.push(['ε']);

        newRules.set(A, newAProds);
        newRules.set(A_prime, newAPrimeProds);
      } else {
        newNonTerminals.push(A);
        newRules.set(A, prods);
      }
    });

    this.rules = newRules;
    this.nonTerminals = [...new Set(newNonTerminals)];
  }

  computeFirstSets() {
    this.firstSets.clear();
    this.nonTerminals.forEach(nt => this.firstSets.set(nt, new Set()));

    let updated = true;
    while (updated) {
      updated = false;
      this.nonTerminals.forEach(A => {
        const prods = this.rules.get(A) || [];
        prods.forEach(prod => {
          const firstProd = this.getFirstOfSequence(prod);
          const currentSet = this.firstSets.get(A);
          const prevSize = currentSet.size;
          firstProd.forEach(s => currentSet.add(s));
          if (currentSet.size > prevSize) updated = true;
        });
      });
    }
  }

  getFirstOfSequence(sequence) {
    const result = new Set();
    if (sequence.length === 0 || sequence[0] === 'ε' || sequence[0] === 'e') {
      result.add('ε');
      return result;
    }

    for (let i = 0; i < sequence.length; i++) {
      const symbol = sequence[i];
      if (!this.rules.has(symbol)) {
        result.add(symbol);
        break;
      } else {
        const symbolFirst = this.firstSets.get(symbol) || new Set();
        let hasEpsilon = false;
        symbolFirst.forEach(s => {
          if (s === 'ε' || s === 'e') hasEpsilon = true;
          else result.add(s);
        });
        if (!hasEpsilon) break;
        if (i === sequence.length - 1) result.add('ε');
      }
    }
    return result;
  }

  computeFollowSets() {
    this.followSets.clear();
    this.nonTerminals.forEach(nt => this.followSets.set(nt, new Set()));
    if (this.startSymbol) this.followSets.get(this.startSymbol).add('$');

    let updated = true;
    while (updated) {
      updated = false;
      this.nonTerminals.forEach(A => {
        const prods = this.rules.get(A) || [];
        prods.forEach(prod => {
          for (let i = 0; i < prod.length; i++) {
            const B = prod[i];
            if (this.rules.has(B)) {
              const beta = prod.slice(i + 1);
              const firstBeta = this.getFirstOfSequence(beta);
              const followB = this.followSets.get(B);
              const prevSize = followB.size;

              firstBeta.forEach(s => {
                if (s !== 'ε' && s !== 'e') followB.add(s);
              });

              if (beta.length === 0 || firstBeta.has('ε') || firstBeta.has('e')) {
                const followA = this.followSets.get(A) || new Set();
                followA.forEach(s => followB.add(s));
              }

              if (followB.size > prevSize) updated = true;
            }
          }
        });
      });
    }
  }

  buildParsingTable() {
    this.parsingTable.clear();
    this.hasConflicts = false;

    this.nonTerminals.forEach(A => this.parsingTable.set(A, new Map()));

    this.nonTerminals.forEach(A => {
      const prods = this.rules.get(A) || [];
      prods.forEach(prod => {
        const firstProd = this.getFirstOfSequence(prod);

        firstProd.forEach(a => {
          if (a !== 'ε' && a !== 'e') {
            this.addTableEntry(A, a, prod);
          }
        });

        if (firstProd.has('ε') || firstProd.has('e')) {
          const followA = this.followSets.get(A) || new Set();
          followA.forEach(b => {
            this.addTableEntry(A, b, prod);
          });
        }
      });
    });
  }

  addTableEntry(A, a, prod) {
    const row = this.parsingTable.get(A);
    if (!row.has(a)) row.set(a, []);
    const cell = row.get(a);
    cell.push(prod);
    if (cell.length > 1) this.hasConflicts = true;
  }

  toString() {
    let res = [];
    this.rules.forEach((prods, head) => {
      const altStr = prods.map(p => p.join(' ')).join(' | ');
      res.push(`${head} -> ${altStr}`);
    });
    return res.join('\n');
  }
}

// Clean AST Diagram Visualizer (Dev Tool Style)
class ParseTreeVisualizer {
  constructor(containerId) {
    this.container = document.getElementById(containerId);
  }

  render(rootNode) {
    if (!rootNode) return;
    this.container.innerHTML = '';

    const svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
    svg.setAttribute('width', '100%');
    svg.setAttribute('height', '320');

    this.drawNode(svg, rootNode, 450, 40, 200);
    this.container.appendChild(svg);
  }

  drawNode(svg, node, x, y, xOffset) {
    if (node.children && node.children.length > 0) {
      const childCount = node.children.length;
      node.children.forEach((child, idx) => {
        const childX = x - (xOffset / 2) + (childCount > 1 ? (idx * (xOffset / (childCount - 1))) : (xOffset / 2));
        const childY = y + 55;

        const line = document.createElementNS('http://www.w3.org/2000/svg', 'line');
        line.setAttribute('x1', x);
        line.setAttribute('y1', y + 10);
        line.setAttribute('x2', childX);
        line.setAttribute('y2', childY - 10);
        line.setAttribute('stroke', '#3f3f46');
        line.setAttribute('stroke-width', '1.5');
        svg.appendChild(line);

        this.drawNode(svg, child, childX, childY, xOffset / 1.8);
      });
    }

    // Render node as a dev-tool badge (rounded rectangle)
    const rect = document.createElementNS('http://www.w3.org/2000/svg', 'rect');
    rect.setAttribute('x', x - 18);
    rect.setAttribute('y', y - 12);
    rect.setAttribute('width', '36');
    rect.setAttribute('height', '24');
    rect.setAttribute('rx', '4');
    rect.setAttribute('fill', node.isTerminal ? '#10b981' : '#2563eb');
    rect.setAttribute('stroke', node.isTerminal ? '#059669' : '#1d4ed8');
    rect.setAttribute('stroke-width', '1');
    svg.appendChild(rect);

    const text = document.createElementNS('http://www.w3.org/2000/svg', 'text');
    text.setAttribute('x', x);
    text.setAttribute('y', y + 4);
    text.setAttribute('text-anchor', 'middle');
    text.setAttribute('fill', '#ffffff');
    text.setAttribute('font-family', 'Geist Mono, Fira Code, monospace');
    text.setAttribute('font-weight', '600');
    text.setAttribute('font-size', '11px');
    text.textContent = node.label;
    svg.appendChild(text);
  }
}

// Application State & Navigation Logic
const engine = new GrammarEngine();
const treeVisualizer = new ParseTreeVisualizer('parseTreeCanvas');
let simState = null;

const GRAMMAR_PRESETS = {
  arithmetic: `E -> E + T | T\nT -> T * F | F\nF -> ( E ) | id`,
  danglingElse: `S -> i E t S | i E t S e S | a\nE -> b`,
  simpleExpr: `E -> T E'\nE' -> + T E' | ε\nT -> F T'\nT' -> * F T' | ε\nF -> ( E ) | id`
};

function switchPage(pageId) {
  document.querySelectorAll('.page-view').forEach(el => el.classList.remove('active'));
  document.querySelectorAll('.tab-btn').forEach(el => el.classList.remove('active'));
  
  document.getElementById(pageId)?.classList.add('active');
  document.querySelector(`[data-page="${pageId}"]`)?.classList.add('active');
}

document.querySelectorAll('.tab-btn').forEach(btn => {
  btn.addEventListener('click', () => switchPage(btn.dataset.page));
});

document.getElementById('grammarPresets')?.addEventListener('change', (e) => {
  const selected = e.target.value;
  if (GRAMMAR_PRESETS[selected]) {
    document.getElementById('grammarInput').value = GRAMMAR_PRESETS[selected];
    document.getElementById('btnComputeSets').click();
  }
});

document.getElementById('btnEliminateLR').addEventListener('click', () => {
  engine.parseInput(document.getElementById('grammarInput').value);
  engine.eliminateLeftRecursion();
  document.getElementById('refinedGrammarOutput').textContent = engine.toString();
});

document.getElementById('btnComputeSets').addEventListener('click', () => {
  engine.parseInput(document.getElementById('grammarInput').value);
  engine.computeFirstSets();
  engine.computeFollowSets();
  engine.buildParsingTable();

  document.getElementById('refinedGrammarOutput').textContent = engine.toString();
  renderFirstFollow();
  renderTable();
  updateStatusBadges();
  switchPage('page2');
});

document.getElementById('btnToPage3').addEventListener('click', () => switchPage('page3'));

function renderFirstFollow() {
  let html = '<table><thead><tr><th>Non-Terminal</th><th>FIRST Set</th><th>FOLLOW Set</th></tr></thead><tbody>';
  engine.nonTerminals.forEach(nt => {
    const first = Array.from(engine.firstSets.get(nt) || []).join(', ');
    const follow = Array.from(engine.followSets.get(nt) || []).join(', ');
    html += `<tr><td><strong>${nt}</strong></td><td>{ ${first} }</td><td>{ ${follow} }</td></tr>`;
  });
  html += '</tbody></table>';
  document.getElementById('firstFollowContainer').innerHTML = html;
}

function renderTable() {
  const terms = Array.from(engine.terminals);
  let html = '<table><thead><tr><th>Non-Terminal</th>';
  terms.forEach(t => html += `<th>${t}</th>`);
  html += '</tr></thead><tbody>';

  engine.nonTerminals.forEach(nt => {
    html += `<tr><td><strong>${nt}</strong></td>`;
    const row = engine.parsingTable.get(nt);
    terms.forEach(t => {
      const cell = row ? row.get(t) : null;
      if (cell && cell.length > 0) {
        const isConflict = cell.length > 1;
        const cellText = cell.map(p => `${nt} -> ${p.join(' ')}`).join('<br>');
        html += `<td class="${isConflict ? 'conflict' : ''}">${cellText}</td>`;
      } else {
        html += '<td></td>';
      }
    });
    html += '</tr>';
  });
  html += '</tbody></table>';

  document.getElementById('ll1TableContainer').innerHTML = html;
}

function updateStatusBadges() {
  const badge = document.getElementById('badgeLL1Status');
  if (!badge) return;

  if (engine.hasConflicts) {
    badge.textContent = 'Conflict Detected';
    badge.className = 'status-badge danger';
  } else {
    badge.textContent = 'LL(1) Valid';
    badge.className = 'status-badge success';
  }
}

// Parsing Simulator Execution
document.getElementById('btnStartSim').addEventListener('click', () => {
  if (!engine.startSymbol) {
    alert('Please compute sets and build the parsing engine first.');
    return;
  }

  const tokens = document.getElementById('simInput').value.trim().split(/\s+/).filter(Boolean);
  tokens.push('$');

  const rootNode = { label: engine.startSymbol, isTerminal: false, children: [] };

  simState = {
    stack: ['$', engine.startSymbol],
    nodeStack: [null, rootNode],
    rootNode: rootNode,
    inputBuffer: tokens,
    pointer: 0,
    steps: [],
    completed: false
  };

  document.getElementById('btnStepSim').disabled = false;
  renderSimLog();
  treeVisualizer.render(simState.rootNode);
});

document.getElementById('btnStepSim').addEventListener('click', () => {
  if (!simState || simState.completed) return;

  const stackTop = simState.stack[simState.stack.length - 1];
  const currentToken = simState.inputBuffer[simState.pointer];

  const currentStackStr = [...simState.stack].join(' ');
  const currentInputStr = simState.inputBuffer.slice(simState.pointer).join(' ');

  if (stackTop === '$' && currentToken === '$') {
    simState.steps.push({ stack: currentStackStr, input: currentInputStr, action: 'ACCEPT: Input string matches grammar' });
    simState.completed = true;
    document.getElementById('btnStepSim').disabled = true;
  } else if (stackTop === currentToken) {
    simState.stack.pop();
    simState.nodeStack.pop();
    simState.pointer++;
    simState.steps.push({ stack: currentStackStr, input: currentInputStr, action: `Shift terminal '${currentToken}'` });
  } else if (!engine.rules.has(stackTop)) {
    simState.steps.push({ stack: currentStackStr, input: currentInputStr, action: `REJECT: Expected '${stackTop}', encountered '${currentToken}'` });
    simState.completed = true;
    document.getElementById('btnStepSim').disabled = true;
  } else {
    const row = engine.parsingTable.get(stackTop);
    const cell = row ? row.get(currentToken) : null;

    if (!cell || cell.length === 0) {
      simState.steps.push({ stack: currentStackStr, input: currentInputStr, action: `REJECT: No table entry for M[${stackTop}, ${currentToken}]` });
      simState.completed = true;
      document.getElementById('btnStepSim').disabled = true;
    } else {
      const prod = cell[0];
      simState.stack.pop();
      const currNode = simState.nodeStack.pop();

      if (prod[0] !== 'ε' && prod[0] !== 'e') {
        const children = prod.map(symbol => ({
          label: symbol,
          isTerminal: !engine.rules.has(symbol),
          children: []
        }));
        if (currNode) currNode.children = children;

        for (let i = prod.length - 1; i >= 0; i--) {
          simState.stack.push(prod[i]);
          simState.nodeStack.push(children[i]);
        }
      } else {
        if (currNode) currNode.children = [{ label: 'ε', isTerminal: true, children: [] }];
      }

      simState.steps.push({ stack: currentStackStr, input: currentInputStr, action: `Reduce: ${stackTop} -> ${prod.join(' ')}` });
    }
  }

  renderSimLog();
  treeVisualizer.render(simState.rootNode);
});

function renderSimLog() {
  if (!simState) return;
  let html = '<table><thead><tr><th>Step</th><th>Parsing Stack</th><th>Input Buffer</th><th>Engine Action</th></tr></thead><tbody>';
  simState.steps.forEach((s, idx) => {
    html += `<tr><td>${idx + 1}</td><td>${s.stack}</td><td>${s.input}</td><td>${s.action}</td></tr>`;
  });
  html += '</tbody></table>';
  document.getElementById('simLogContainer').innerHTML = html;
}