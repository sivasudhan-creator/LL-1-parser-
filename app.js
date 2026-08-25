// ==========================================
// Grammar Engine Class
// ==========================================
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
    this.conflictsList = [];
  }

  parseInput(inputText) {
    this.rules.clear();
    this.nonTerminals = [];
    this.terminals.clear();
    this.startSymbol = null;

    const lines = inputText.split('\n');

    lines.forEach(line => {
      const trimmed = line.trim();
      if (!trimmed || trimmed.startsWith('#')) return;

      const parts = trimmed.split('->');
      if (parts.length < 2) return;

      const head = parts[0].trim();
      if (!this.startSymbol) this.startSymbol = head;
      if (!this.nonTerminals.includes(head)) this.nonTerminals.push(head);

      const productions = parts[1].split('|').map(prod => 
        prod.trim().split(/\s+/).filter(token => token !== '')
      );

      if (!this.rules.has(head)) {
        this.rules.set(head, []);
      }
      this.rules.get(head).push(...productions);
    });

    this.rules.forEach((prods) => {
      prods.forEach(prod => {
        prod.forEach(symbol => {
          if (!this.nonTerminals.includes(symbol) && symbol !== 'ε' && symbol !== 'e') {
            this.terminals.add(symbol);
          }
        });
      });
    });
    this.terminals.add('$');

    this.computeFirstSets();
    this.computeFollowSets();
    this.buildParsingTable();
  }

  computeFirstSets() {
    this.firstSets.clear();
    this.nonTerminals.forEach(nt => this.firstSets.set(nt, new Set()));

    let changed = true;
    while (changed) {
      changed = false;
      this.nonTerminals.forEach(A => {
        const prods = this.rules.get(A) || [];
        const firstA = this.firstSets.get(A);
        const beforeSize = firstA.size;

        prods.forEach(prod => {
          let allHaveEpsilon = true;

          for (const symbol of prod) {
            if (symbol === 'ε' || symbol === 'e') {
              firstA.add('ε');
              break;
            } else if (this.terminals.has(symbol)) {
              firstA.add(symbol);
              allHaveEpsilon = false;
              break;
            } else {
              const firstSym = this.firstSets.get(symbol) || new Set();
              firstSym.forEach(val => {
                if (val !== 'ε') firstA.add(val);
              });

              if (!firstSym.has('ε')) {
                allHaveEpsilon = false;
                break;
              }
            }
          }

          if (allHaveEpsilon && prod.length > 0) {
            firstA.add('ε');
          }
        });

        if (firstA.size > beforeSize) changed = true;
      });
    }
  }

  getFirstOfSequence(sequence) {
    const result = new Set();
    let allHaveEpsilon = true;

    for (const symbol of sequence) {
      if (symbol === 'ε' || symbol === 'e') {
        result.add('ε');
        break;
      } else if (this.terminals.has(symbol)) {
        result.add(symbol);
        allHaveEpsilon = false;
        break;
      } else {
        const firstSym = this.firstSets.get(symbol) || new Set();
        firstSym.forEach(val => {
          if (val !== 'ε') result.add(val);
        });

        if (!firstSym.has('ε')) {
          allHaveEpsilon = false;
          break;
        }
      }
    }

    if (allHaveEpsilon) result.add('ε');
    return result;
  }

  computeFollowSets() {
    this.followSets.clear();
    this.nonTerminals.forEach(nt => this.followSets.set(nt, new Set()));

    if (this.startSymbol) {
      this.followSets.get(this.startSymbol).add('$');
    }

    let changed = true;
    while (changed) {
      changed = false;

      this.nonTerminals.forEach(A => {
        const prods = this.rules.get(A) || [];

        prods.forEach(prod => {
          for (let i = 0; i < prod.length; i++) {
            const B = prod[i];
            if (this.nonTerminals.includes(B)) {
              const followB = this.followSets.get(B);
              const beforeSize = followB.size;

              const beta = prod.slice(i + 1);
              const firstBeta = this.getFirstOfSequence(beta);

              firstBeta.forEach(val => {
                if (val !== 'ε') followB.add(val);
              });

              if (firstBeta.has('ε') || beta.length === 0) {
                const followA = this.followSets.get(A) || new Set();
                followA.forEach(val => followB.add(val));
              }

              if (followB.size > beforeSize) changed = true;
            }
          }
        });
      });
    }
  }

  eliminateLeftRecursion() {
    const newRules = new Map();
    const newNonTerminals = [];
    const stepsLog = [];

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

        stepsLog.push(
          `Step 1: Left recursion detected in '${A}'\n  ${A} -> ${prods.map(p => p.join(' ')).join(' | ')}\n\n` +
          `Step 2: Removing left recursion...\n\n` +
          `Step 3: Refined grammar:\n  ${A} -> ${newAProds.map(p => p.join(' ')).join(' | ')}\n  ${A_prime} -> ${newAPrimeProds.map(p => p.join(' ')).join(' | ')}`
        );
      } else {
        newNonTerminals.push(A);
        newRules.set(A, prods);
      }
    });

    this.rules = newRules;
    this.nonTerminals = [...new Set(newNonTerminals)];

    this.computeFirstSets();
    this.computeFollowSets();
    this.buildParsingTable();

    return stepsLog.length > 0 
      ? stepsLog.join('\n\n----------------------------------------\n\n') 
      : 'No left recursion detected in this grammar.';
  }

  buildParsingTable() {
    this.parsingTable.clear();
    this.hasConflicts = false;
    this.conflictsList = [];

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

    const prodStr = prod.join(' ');

    if (cell.length > 0) {
      const existingProdStr = cell[0].join(' ');
      if (existingProdStr !== prodStr) {
        this.hasConflicts = true;
        const prod1Str = `${A} -> ${existingProdStr}`;
        const prod2Str = `${A} -> ${prodStr}`;

        const isAlreadyLogged = this.conflictsList.some(
          c => c.cell === `M[${A}, ${a}]` && c.prod2 === prod2Str
        );

        if (!isAlreadyLogged) {
          this.conflictsList.push({
            cell: `M[${A}, ${a}]`,
            prod1: prod1Str,
            prod2: prod2Str,
            reason: 'Multiple productions require the same table entry.'
          });
        }
      }
    }

    cell.push(prod);
  }
}

// ==========================================
// Parsing Simulator Engine (Page 3)
// ==========================================
class SimulatorEngine {
  constructor(grammarEngine) {
    this.engine = grammarEngine;
    this.stack = [];
    this.inputTokens = [];
    this.tokenIndex = 0;
    this.stepHistory = [];
    this.isFinished = false;
    this.treeData = null;
  }

  init(inputStr) {
    this.stack = ['$', this.engine.startSymbol];
    this.inputTokens = inputStr.trim().split(/\s+/).filter(t => t !== '');
    this.inputTokens.push('$');
    this.tokenIndex = 0;
    this.stepHistory = [];
    this.isFinished = false;

    this.treeData = {
      name: this.engine.startSymbol,
      children: []
    };

    this.logStep('Initialization', 'Stack initialized with start symbol.');
  }

  logStep(action, ruleUsed = '') {
    const remainingInput = this.inputTokens.slice(this.tokenIndex).join(' ');
    const stackStr = [...this.stack].reverse().join(' ');
    this.stepHistory.push({
      step: this.stepHistory.length + 1,
      stack: stackStr,
      input: remainingInput,
      action: action,
      rule: ruleUsed
    });
  }

  step() {
    if (this.isFinished) return false;

    const top = this.stack[this.stack.length - 1];
    const currentToken = this.inputTokens[this.tokenIndex];

    if (top === '$' && currentToken === '$') {
      this.stack.pop();
      this.logStep('Accepted', 'String successfully parsed!');
      this.isFinished = true;
      return false;
    }

    if (top === currentToken) {
      this.stack.pop();
      this.tokenIndex++;
      this.logStep(`Matched '${currentToken}'`, '');
      return true;
    }

    if (this.engine.nonTerminals.includes(top)) {
      const row = this.engine.parsingTable.get(top);
      const cell = row ? row.get(currentToken) : null;

      if (!cell || cell.length === 0) {
        this.logStep('Error', `No production for M[${top}, ${currentToken}]`);
        this.isFinished = true;
        return false;
      }

      const prod = cell[0];
      this.stack.pop();

      if (prod[0] !== 'ε' && prod[0] !== 'e') {
        for (let i = prod.length - 1; i >= 0; i--) {
          this.stack.push(prod[i]);
        }
      }

      const ruleStr = `${top} -> ${prod.join(' ')}`;
      this.logStep(`Apply ${ruleStr}`, ruleStr);
      return true;
    }

    this.logStep('Error', `Unexpected token '${currentToken}'`);
    this.isFinished = true;
    return false;
  }
}

// ==========================================
// UI Rendering & Event Handling
// ==========================================
const engine = new GrammarEngine();
const simulator = new SimulatorEngine(engine);

function renderFirstFollow() {
  const container = document.getElementById('firstFollowContainer');
  if (!container) return;

  let html = '<table><thead><tr><th>Non-Terminal</th><th>FIRST</th><th>FOLLOW</th></tr></thead><tbody>';

  engine.nonTerminals.forEach(nt => {
    const firstSet = Array.from(engine.firstSets.get(nt) || []).join(', ');
    const followSet = Array.from(engine.followSets.get(nt) || []).join(', ');
    html += `<tr><td><strong>${nt}</strong></td><td>{ ${firstSet} }</td><td>{ ${followSet} }</td></tr>`;
  });

  html += '</tbody></table>';
  container.innerHTML = html;
}

function renderTable() {
  const container = document.getElementById('ll1TableContainer');
  const badge = document.getElementById('badgeLL1Status');
  if (!container) return;

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
        html += `<td style="${isConflict ? 'background-color: rgba(239, 68, 68, 0.2); color: #f87171;' : ''}">${cellText}</td>`;
      } else {
        html += '<td></td>';
      }
    });
    html += '</tr>';
  });
  html += '</tbody></table>';

  if (badge) {
    if (engine.hasConflicts) {
      badge.textContent = 'Non-LL(1) Conflicts';
      badge.className = 'status-badge danger';
    } else {
      badge.textContent = 'LL(1) Valid';
      badge.className = 'status-badge success';
    }
  }

  if (engine.hasConflicts && engine.conflictsList.length > 0) {
    html += `<div style="margin-top: 16px; padding: 16px; background: rgba(239, 68, 68, 0.1); border: 1px solid #dc2626; border-radius: 8px;">`;
    html += `<h4 style="color: #f87171; margin: 0 0 12px 0;">⚠ LL(1) Conflict Detected</h4>`;

    engine.conflictsList.forEach(c => {
      html += `<div style="font-family: monospace; font-size: 13px; margin-bottom: 12px; color: #f4f4f5; line-height: 1.5;">`;
      html += `<div><strong>Table Entry:</strong> ${c.cell}</div>`;
      html += `<div><strong>Production 1:</strong> ${c.prod1}</div>`;
      html += `<div><strong>Production 2:</strong> ${c.prod2}</div>`;
      html += `<div style="color: #f87171;"><strong>Reason:</strong> ${c.reason}</div>`;
      html += `</div>`;
    });

    html += `</div>`;
  }

  container.innerHTML = html;
}

function renderSimLog() {
  const container = document.getElementById('simLogContainer');
  if (!container) return;

  let html = '<table><thead><tr><th>Step</th><th>Stack</th><th>Input</th><th>Action</th></tr></thead><tbody>';

  simulator.stepHistory.forEach(s => {
    html += `<tr><td>${s.step}</td><td style="font-family: monospace;">${s.stack}</td><td style="font-family: monospace;">${s.input}</td><td>${s.action}</td></tr>`;
  });

  html += '</tbody></table>';
  container.innerHTML = html;
}

function renderSimpleAST() {
  const canvas = document.getElementById('parseTreeCanvas');
  if (!canvas) return;

  if (simulator.stepHistory.length === 0) {
    canvas.innerHTML = `<p class="placeholder-text">Tree will generate progressively during stepping.</p>`;
    return;
  }

  let treeHtml = `<div style="padding: 16px; font-family: monospace; color: #38bdf8;">`;
  treeHtml += `<strong>Generated Execution Steps:</strong><br><br>`;
  simulator.stepHistory.forEach(s => {
    if (s.rule) treeHtml += `• ${s.rule}<br>`;
  });
  treeHtml += `</div>`;

  canvas.innerHTML = treeHtml;
}

function updateAll() {
  const input = document.getElementById('grammarInput');
  if (input) {
    engine.parseInput(input.value);
    renderFirstFollow();
    renderTable();
  }
}

// Preset Handler
const presets = {
  arithmetic: "E -> E + T | T\nT -> T * F | F\nF -> ( E ) | id",
  danglingElse: "S -> i C t S S' | a\nS' -> e S | ε\nC -> b",
  simpleExpr: "E -> T E'\nE' -> + T E' | ε\nT -> F T'\nT' -> * F T' | ε\nF -> ( E ) | id"
};

document.addEventListener('DOMContentLoaded', () => {
  const grammarInput = document.getElementById('grammarInput');
  const btnEliminateLR = document.getElementById('btnEliminateLR');
  const btnStartSim = document.getElementById('btnStartSim');
  const btnStepSim = document.getElementById('btnStepSim');
  const grammarPresets = document.getElementById('grammarPresets');

  if (grammarInput) {
    grammarInput.addEventListener('input', updateAll);
    updateAll();
  }

  if (grammarPresets) {
    grammarPresets.addEventListener('change', (e) => {
      const val = e.target.value;
      if (presets[val]) {
        grammarInput.value = presets[val];
        updateAll();
      }
    });
  }

  if (btnEliminateLR) {
    btnEliminateLR.addEventListener('click', () => {
      if (grammarInput) engine.parseInput(grammarInput.value);
      const explanation = engine.eliminateLeftRecursion();
      
      const outputElem = document.getElementById('refinedGrammarOutput');
      if (outputElem && grammarInput) {
        let cleanGrammar = '';
        engine.rules.forEach((prods, head) => {
          cleanGrammar += `${head} -> ${prods.map(p => p.join(' ')).join(' | ')}\n`;
        });
        grammarInput.value = cleanGrammar.trim();
        outputElem.textContent = explanation;
      }
      
      renderFirstFollow();
      renderTable();
    });
  }

  if (btnStartSim) {
    btnStartSim.addEventListener('click', () => {
      const simInput = document.getElementById('simInput');
      const inputStr = simInput ? simInput.value : 'id + id * id';
      
      updateAll();
      simulator.init(inputStr);
      renderSimLog();
      renderSimpleAST();

      if (btnStepSim) btnStepSim.disabled = false;
    });
  }

  if (btnStepSim) {
    btnStepSim.addEventListener('click', () => {
      const hasMore = simulator.step();
      renderSimLog();
      renderSimpleAST();

      if (!hasMore || simulator.isFinished) {
        btnStepSim.disabled = true;
      }
    });
  }
});
