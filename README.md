# Conflict-Free Cut: finite verification

Can a network be disconnected when some pairs of links may not be removed
together? A **conflict-free cut** answers that question without selecting both
links of any forbidden pair.

This repository contains a self-contained checker for a CNF-SAT to
Conflict-Free Cut reduction. A formula on `n` variables produces a graph with
an explicit vertex cover of size `n + 2`, independently of the number and
lengths of its clauses. The code checks the reduction on finite instances.
It is a reproducibility companion to the author-review manuscript
*No polynomial compression for conflict-free cuts with small vertex cover*.

The repository contains verification code and its documentation. The manuscript
and submission correspondence are not hosted here.

## Run

Requirements: **Python 3.8+**, standard library only. No installation, network
service, SAT solver, or graph package is needed. From the repository root:

```bash
python3 verification/verify_reduction.py --output verification/results.json
```

The script prints its results and writes the JSON file. Use normal Python
execution; do not use `python -O` or `PYTHONOPTIMIZE`, because the checks use
assertions. Exhaustive bipartition enumeration grows exponentially, so the
default suite intentionally uses small graphs.

## What is checked

The constructor creates the primary graph and all conflict pairs. An independent
oracle enumerates every nontrivial vertex bipartition with `a` fixed on side 0,
including partitions placing `b` on side 0. It computes the crossing edges and
tests every conflict directly. It then compares the projected variable labels
with a separately evaluated CNF truth table.

Structural checks verify the explicit cover of size `n + 2`, the two universal
vertices, the star forest left after deleting them, the exact graph sizes, and
the conflict forest's component sizes, degrees, and central radius. A separate
16-row truth-table check enumerates both choices of each private witness.

The deterministic default suite covers:

| Check | Count |
| --- | ---: |
| All subsets of the eight canonical two-variable clauses | 256 formulas |
| Seeded random formulas, seed `20261021` | 400 formulas |
| Explicit edge cases | 7 formulas |
| Total formulas | 663 |
| Enumerated graph bipartitions | 4,949,325 |
| Accepted conflict-free cuts | 3,155 |
| Largest primary graph | 20 vertices |
| Local gadget truth-table rows | 16 |

Expected final status: `PASS`. Runtime is recorded for convenience and is not a
benchmark. The JSON output also records the SHA-256 hash of the executed script.

## Input convention and limits

`construct(n, clauses)` accepts `n >= 1` and nonempty clauses of signed variable
indices: `1` means `x1`, and `-1` means its negation. An empty conjunction is
supported. A formula containing an empty clause must first be replaced by the
fixed contradiction `(x1) AND (NOT x1)`.

These finite checks can expose construction and implementation errors. They do
not prove correctness for all formulas, certify novelty, or replace the
mathematical proof or independent review. The lower bound in the manuscript
uses the standard assumption `NP` is not contained in `coNP/poly`.

## Code map

- `construct`: builds the two graphs from a CNF formula.
- `satisfying_assignments`: independently evaluates the formula.
- `graph_projection`: enumerates graph cuts directly, using Gray-code updates.
- `structural_check`: checks graph sizes and promised structure.
- `gate_check`: checks the local two-conflict gadget.
- `main`: runs the deterministic suite and records results.

OpenAI ChatGPT assisted in developing the reduction, drafting its proof, and
writing this verification code. The accompanying manuscript remains an
author-review draft.
