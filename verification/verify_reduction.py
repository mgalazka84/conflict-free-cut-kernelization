#!/usr/bin/env python3
"""Independent finite checks for the CNF-SAT to Conflict-Free Cut reduction.

Python 3 standard library only. No SAT solver or graph package is required.
The exhaustive oracle enumerates graph bipartitions and tests conflicting
crossing edges directly; it does not use the gadget's logical recurrence.
Run: python3 verification/verify_reduction.py --output verification/results.json
"""
import argparse
import hashlib
import itertools
import json
import random
import time
from pathlib import Path


def construct(n, clauses):
    """Nonempty clauses use signed variable indices in 1,...,n.

    An empty conjunction is supported. Empty clauses must be handled by
    preprocessing (replace the formula by (x_1) AND (NOT x_1)).
    """
    assert n >= 1
    assert all(c and all(1 <= abs(l) <= n for l in c) for c in clauses)
    labels = ['a', 'b'] + [f'x{i+1}' for i in range(n)]
    stages = []
    for j, clause in enumerate(clauses):
        states = [1]
        for i in range(len(clause)-1):
            states.append(len(labels))
            labels.append(f'q{j+1}_{i+1}')
        states.append(0)
        for i, literal in enumerate(clause):
            witness = len(labels)
            labels.append(f'w{j+1}_{i+1}')
            stages.append((states[i], states[i+1], abs(literal)+1,
                           witness, literal > 0))
    edges = []
    edge_ids = {}

    def edge(u, v):
        assert u != v
        key = tuple(sorted((u, v)))
        if key not in edge_ids:
            edge_ids[key] = len(edges)
            edges.append(key)
        return edge_ids[key]

    reference = edge(0, 1)
    for z in range(2, len(labels)):
        edge(0, z)
        edge(1, z)
    for _, _, x, w, _ in stages:
        edge(x, w)
    conflicts = set()

    def conflict(e, f):
        assert e != f
        conflicts.add(tuple(sorted((e, f))))

    for z in range(2, len(labels)):
        conflict(edge(0, z), edge(1, z))
    for p, q, x, w, positive in stages:
        conflict(edge(0, p), edge(x, w))
        conflict(edge(1 if positive else 0, w), edge(1, q))
    return labels, edges, sorted(conflicts), reference


def satisfying_assignments(n, clauses):
    return {bits for bits in range(1 << n)
            if all(any(bool(bits & (1 << (abs(l)-1))) == (l > 0)
                       for l in clause) for clause in clauses)}


def graph_projection(n, labels, edges, conflicts):
    """All nontrivial cuts with a=0, including the forbidden a=b case."""
    incidence = [0] * len(labels)
    for i, (u, v) in enumerate(edges):
        incidence[u] |= 1 << i
        incidence[v] |= 1 << i
    forbidden = [(1 << e) | (1 << f) for e, f in conflicts]
    feasible = set()
    valid_count = 0
    cut_mask = 0
    old_assignment = 0
    for t in range(1, 1 << (len(labels)-1)):
        assignment = (t ^ (t >> 1)) << 1
        changed = (assignment ^ old_assignment).bit_length()-1
        cut_mask ^= incidence[changed]
        old_assignment = assignment
        if any(cut_mask & mask == mask for mask in forbidden):
            continue
        assert assignment & 2, 'Nontrivial cut has a=b'
        feasible.add((assignment >> 2) & ((1 << n)-1))
        valid_count += 1
    return feasible, valid_count, (1 << (len(labels)-1))-1


def structural_check(n, clauses, labels, edges, conflicts, reference):
    m, length = len(clauses), sum(map(len, clauses))
    assert len(labels) == n + 2*length - m + 2
    assert len(edges) == 1 + 2*n + 5*length - 2*m
    assert len(conflicts) == n + 4*length - m
    cover = set(range(n+2))
    assert all(u in cover or v in cover for u, v in edges)
    adjacency = [set() for _ in labels]
    for u, v in edges:
        adjacency[u].add(v)
        adjacency[v].add(u)
    assert len(adjacency[0]) == len(labels)-1
    assert len(adjacency[1]) == len(labels)-1
    assert all(len(adjacency[z]) <= 3 for z in range(n+2, len(labels)))
    assert all(u < n+2 or v < n+2 for u, v in edges)
    # Removing the two universal vertices leaves only variable-witness stars.
    assert all(u < 2 or v < 2 or
               (2 <= u < n+2 and labels[v].startswith('w'))
               for u, v in edges)
    h = [set() for _ in edges]
    for e, f in conflicts:
        h[e].add(f)
        h[f].add(e)
    assert all(len(h[v]) <= 2 for v in range(len(h)) if v != reference)
    assert len(h[reference]) == 2*m
    seen, component_sizes = set(), []
    for root in range(len(h)):
        if root in seen:
            continue
        component, stack = set(), [root]
        while stack:
            v = stack.pop()
            if v in component:
                continue
            component.add(v)
            stack.extend(h[v] - component)
        seen.update(component)
        edge_count = sum(len(h[v]) for v in component)//2
        assert edge_count == len(component)-1, 'Conflict graph is not a forest'
        if reference in component:
            assert len(component) == 1+3*m
            distances = {reference: 0}
            frontier = [reference]
            while frontier:
                v = frontier.pop()
                for w in h[v]:
                    if w not in distances:
                        distances[w] = distances[v]+1
                        frontier.append(w)
            assert max(distances.values()) <= 2
        else:
            component_sizes.append(len(component))
    assert sorted(component_sizes) == sorted([2]*n + [5]*(length-m))


def gate_check():
    checked = 0
    for positive, p, q, x in itertools.product((False, True), repeat=4):
        possible = []
        for w in (False, True):
            first = not (p and (x != w))
            second = not (((not w) if positive else w) and (not q))
            if first and second:
                possible.append(w)
        literal = x if positive else not x
        expected = (not p) or literal or q
        assert bool(possible) == expected
        checked += 1
    return checked


def verify_formula(n, clauses):
    labels, edges, conflicts, reference = construct(n, clauses)
    structural_check(n, clauses, labels, edges, conflicts, reference)
    projection, valid_count, partitions = graph_projection(n, labels, edges, conflicts)
    expected = satisfying_assignments(n, clauses)
    assert projection == expected, (n, clauses, expected, projection)
    return partitions, valid_count, len(labels)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', default='verification/results.json')
    args = parser.parse_args()
    started = time.perf_counter()
    stats = {'seed': 20261021, 'gate_truth_table_rows': gate_check(),
             'exhaustive_two_variable_formulas': 0, 'seeded_formulas': 0,
             'explicit_edge_cases': 0, 'graph_partitions_checked': 0,
             'valid_graph_cuts': 0, 'largest_graph_vertices': 0}

    def record(n, clauses, kind):
        count, valid, vertices = verify_formula(n, clauses)
        stats[kind] += 1
        stats['graph_partitions_checked'] += count
        stats['valid_graph_cuts'] += valid
        stats['largest_graph_vertices'] = max(stats['largest_graph_vertices'], vertices)

    clauses = [(1,), (-1,), (2,), (-2,),
               (1, 2), (1, -2), (-1, 2), (-1, -2)]
    for mask in range(1 << len(clauses)):
        record(2, [c for i, c in enumerate(clauses) if mask & (1 << i)],
               'exhaustive_two_variable_formulas')
    print('All 256 canonical two-variable formulas passed.', flush=True)
    rng = random.Random(stats['seed'])
    for _ in range(400):
        n = rng.randint(1, 3)
        length = rng.randint(1, 6)
        clauses, clause = [], []
        for i in range(length):
            clause.append(rng.choice((-1, 1))*rng.randint(1, n))
            if i == length-1 or rng.random() < 0.4:
                clauses.append(tuple(clause))
                clause = []
        record(n, clauses, 'seeded_formulas')
    for n, formula in [(1, []), (1, [(1,), (-1,)]),
                       (1, [(1, -1)]), (1, [(1, 1), (-1, -1)]),
                       (2, [(1, 2), (1, 2)]),
                       (3, [(1, 2, -3, 1, -2, 3)]),
                       (3, [(1,), (-1,), (2, 3, -2, -3)])]:
        record(n, formula, 'explicit_edge_cases')
    stats['status'] = 'PASS'
    stats['elapsed_seconds'] = round(time.perf_counter()-started, 3)
    stats['verifier_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    output = Path(args.output)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(stats, indent=2)+'\n')
    print(json.dumps(stats, indent=2))


if __name__ == '__main__':
    main()
