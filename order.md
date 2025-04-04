# Decision procedures for order theories

In this post, I describe algorithms that are decision procedures for some theories and discuss their computational complexities. The results can be summarized in the following table:

| Theory               | Complexity    |
|----------------------|---------------|
| Preorder             | P             |
| Partial Order        | P             |
| Linear Order         | P             |
| Lattice              | P             |
| Distributive Lattice | coNP-complete |
| Boolean Algebra      | coNP-complete |

Adding conditions for the existence of `⊤` or `⊥` elements does not change the complexity for each theory. The algorithm for the first four theories is similar and now implemented as the `order` tactic in Mathlib. The approach for the last two is different and not implemented as a tactic so far.

Let me formally state the problem whose complexity is discussed. The input for an algorithm is a set of *atomic facts*, i.e., propositions containing only variables, predicate symbols from the theory (for example `≤`, `<`, and `=` for preorders), and negation. For example, we forbid logical connectives here. The algorithm must derive a contradiction (`False`) from the given set of facts whenever it is possible.

In practice, the `order` tactic negates the goal, splits conjuctions and tries to find the contradiction as described below.

## Algorithms' description

Below I describe the algorithms and show why they are decision procedures. The argument for the latter always uses basic model theory and has the form: "suppose the algorithm cannot find the contradiction, then we show that the given set of facts can be satisfied by some model of the theory, and therefore is not contradictory."

As discussed above, any atomic fact can have one of the following 6 forms:
* `x = y`
* `x ≠ y`
* `x < y`
* `¬(x < y)`
* `x ≤ y`
* `¬(x ≤ y)`

for some terms `x` and `y`. In preorders, partial orders, and linear orders, terms can only be variables. In lattices, they can also contain `⊔` and `⊓` operations. And in Boolean algebras, there are also complement and implication operations.

### Preorder
#### Algorithm description
1. **Preprocessing**.
We replace some facts as follows:
* Replace `x < y` with two equivalent facts: `x ≤ y` and `¬(y ≤ x)`.
* Replace `x = y` with `x ≤ y` and `y ≤ x`.
* Remove `x ≠ y`.
2. **Building the `≤`-graph**.
We construct a graph where vertices correspond to atoms (i.e., atomic terms), and an edge `(x, y)` exists if the fact
`x ≤ y` is present in our set of facts. We call this graph a `≤`-graph. The main property of this graph is that if `x` is reachable from `y` in the graph, then one can derive `y ≤ x`.
3. **Growing the `≤`-graph with `≮`-facts**.
In preorders, `¬(x < y)` is equivalent to `(x ≤ y) → (y ≤ x)`. Thus, if `y` is reachable from `x`
in the `≤`-graph, we can derive the new fact `y ≤ x`. At this step, we add such edges to the graph while possible. To check reachability, we use a simple DFS algorithm. If some `≮`-fact is used, it cannot be used in the future, so the number of iterations of the `while`-loop is bounded by the size of the set of facts.
4. **Finding contradictions using `≰`-facts**.
For each fact `¬(x ≤ y)`, we check if `y` is reachable from `x` in the `≤`-graph using DFS. If so, we derive the desired contradiction.

#### Why is this a decision procedure?
Technically, it is not, because it cannot prove `(x = y) → (y ≠ z) → (x ≠ z)`. Goals involving
only `=` and `≠` can be handled by the `cc` tactic. Assume, then, that a set `T` of facts is
contradictory, but there is no chain `x₁ = x₂ = ... = xₖ` in `T` along with the fact `x₁ ≠ xₖ`. Then
we claim that the described algorithm is able to deduce a contradiction from `T`. Let `T'` be the
set of facts after preprocessing. Then `T'` remains contradictory.

Indeed, suppose that `T'` is satisfiable, i.e., there exists a model `M` that satisfies `T'`.
Consider a quotient `M'` of `M` by the equivalence relation `~`, where `a ~ b` holds for `a ≠ b` iff
both `a` and `b` are values of some variables `x` and `y` from `T`, and there is
a chain `x = ... = y` in `T`. Define the relation `R'` on `M'` as `α R' β` if and only if `a R b`
in `M` for some `a ∈ α` and `b ∈ β`. Then `M'` is a model satisfying `T`:
* For any fact `x = y` in `T`, we have `M'(x) = M'(y)` in `M'`.
* For any fact `x ≠ y` in `T`, we have `M'(x) ≠ M'(y)`, since otherwise, there would exist
  a chain `x = ... = y` in `T`.
* For any fact `x ≤ y` in `T`, and thus in `T'`, we have `M(x) R M(y)`, so `M'(x) R' M'(y)`.
* For any fact `¬(x ≤ y)` in `T`, and thus in `T'`, we have `¬M(x) R M(y)`. Then, for any `x' ~ x`
  and `y' ~ y`, we can deduce `x ≤ x'` and `y' ≤ y` from `T'`. If `M(x') R M(y')`, then
  `M(x) R M(x') R M(y') R M(y)`, which contradicts the assumption that `M` is a model of `T'`.
  This contradiction implies that `¬M'(x) R' M'(y)`, as required.

If, at step 6, no contradictory `≰`-facts were found, we must show that a model satisfies `T'`.
A suitable model can be constructed using the connected components of the `=`-graph (defined
similarly to the `≤`-graph),
with the relation `R` defined as `C₁ R C₂` iff `C₂` is reachable from `C₁` in the `≤`-graph. Each
variable `x` is interpreted as its component `[x]`. This forms a preorder, and we verify that each
fact in `T'` is satisfied:
* `x = y` is satisfied because `x` and `y` must be in the same component in the `=`-graph.
* `x ≤ y` is satisfied by the construction of the `≤`-graph.
* `x ≠ y` is satisfied because otherwise, `x` and `y` would belong to the same component in
the `=`-graph, contradicting our initial assumption.
* `¬(x < y)` is satisfied because otherwise `¬[y] R [x]`, meaning there is a path from `x` to `y`,
which would have caused an edge `(y, x)` to be added at step 5, leading to a contradiction.

### Partial Order
1. **Preprocessing**.
We replace some facts as follows:
* Replace `x < y` with `x ≤ y` and `x ≠ y`.
* Replace `x = y` with `x ≤ y` and `y ≤ x`.
* Replace `¬(x ≤ y)` with `x ≠ y` and `¬(x < y)`.
2. **Building the `≤`-graph**: Same as for preorders.
3. **Growing the `≤`-graph with `≮`-facts**: Same as for preorders.
4. **Finding contradictions using `≠`-facts**.
We identify strongly connected components in the `≤`-graph using Tarjan's algorithm. For each
fact `x ≠ y`, we check whether `x` and `y` belong to the same component. If they do, then `x = y` is provable, contradicting `x ≠ y`.

#### Why is this a decision procedure?
Assume that a set `T` of facts is contradictory. We must show that the described algorithm can
derive a contradiction. Let `T'` be the set of facts after preprocessing. By construction, `T'` is
also contradictory (they are equisatisfiable). Suppose at step 6 no contradictory `≠`-facts were found. We then show that a model satisfies `T'`. A suitable model is the set of strongly connected
components of the `≤`-graph, with the relation `R` defined as `C₁ R C₂` iff `C₂` is reachable from `C₁`. Each variable `x` is interpreted as its component `[x]`. This forms a partial order, and
we verify that each fact in `T'` is satisfied:
* `x ≤ y` is satisfied because it directly implies `[x] R [y]`.
* `x ≠ y` is satisfied because otherwise, `x` and `y` would belong to the same component, leading to
a contradiction at step 6.
* `¬(x < y)` is satisfied because otherwise `[x] ≠ [y]` and there is a path from `x` to `y`, which
would have merged them into the same component at step 5.

### Linear Order
1. **Preprocessing**.
We replace some facts as follows:
* Replace `x < y` with `x ≤ y` and `x ≠ y`.
* Replace `x = y` with `x ≤ y` and `y ≤ x`.
* Replace `¬(x ≤ y)` with `x ≠ y` and `y ≤ x`.
* Replace `¬(x < y)` with `y ≤ x`.
2. **Building the `≤`-graph**: Same as for preorders.
3. **Finding contradictions using `≠`-facts**: Same as for partial orders.

Note that the algorithm for linear orders is simply the algorithm for partial orders with an
additional preprocessing step. It also skips the growing step because there are no `≮`-facts.

#### Why is this a decision procedure?
We need to slightly modify the proof for partial orders. In this case, `T` and `T'` are again
equisatisfiable. Suppose the algorithm cannot find a contradiction, and construct the model of `T'`.
The carrier of the model is once again the set of strongly connected components in the `≤`-graph,
with variables interpreted as their respective components. Note that the reachability relation
(used before) on components is acyclic. Therefore, it can be
[topologically ordered](https://en.wikipedia.org/wiki/Topological_sorting), meaning it forms a
linear order where `C₁ R C₂` whenever `C₂` is reachable from `C₁`. It is easy to see that all facts
in `T'` are satisfied by the model.

### Lattice
In this case, there are new types of atomic facts, namely:
* `x ⊔ y = z`
* `x ⊓ y = z`

where `x`, `y`, and `z` are variables.
The algorithm for lattices is similar to that for partial orders, with two differences:
1. During the preprocessing step, for each fact `x ⊔ y = z`, we add the facts `x ≤ z` and `y ≤ z`, and similarly for `⊓`.
2. In step 5, we, in addition to the above, expand the `≤`-graph using the following procedure: if a vertex `v` is reachable
from both `x` and `y`, and `x ⊔ y = z` is present in the set of facts, we add the edge `(z, v)`
using `sup_le`, and similarly for `⊓`.


#### Why is this a decision procedure?
Again, suppose that the algorithm does not find a contradiction from some set `T`, and construct the lattice that satisfies `T`. Consider the constructed `≤`-graph `G`.
Let us denote `Sup(x, y, z)` as the predicate on vertices of some graph stating that the
vertex `z` is reachable from both `x` and `y`, and
for any vertex `v` reachable from both `x` and `y`, there is a path from `z` to `v`.
Also denote `HasSup(x, y) = ∃ z, Sup(x, y, z)`, and define `Inf(x, y, z)` and `HasInf(x, y)`
symmetrically. Note that if there is a fact `x ⊔ y = z` in `T'`, then `Sup(x, y, z)` is true for the
graph `G`.

We construct a new graph `H` from `G` as follows.
For all pairs `x`, `y` of variables from `T'`, if there is no
fact `x ⊔ y = z` for some `z` in `T'`, we add a new vertex `z` in the graph with
edges `(x, z)`, `(y, z)`, and `(z, v)` for all `v` that is reachable from both `x` and `y` in `G`,
and symmetrically for `⊓`.

The graph `H` has the following property: for any two variables `x` and `y` from `T'`, there is a
vertex `z` such that `z` is reachable from both `x` and `y`, and for any vertex `v` reachable from
both `x` and `y`, there is a path from `z` to `v`. In such a case, we call the vertex `z` as `x ⊔ᵣ y`.
The operation `⊓ᵣ` is defined symmetrically.

Let `G₀ = G`. We construct the sequence `Gₖ` of graphs recursively as follows. `Gₖ₊₁` extends `Gₖ`
using the following procedure.
For all pairs `x`, `y` of vertices from `Gₖ`, if `HasSup(x, y)` does not hold, we add a new vertex
`z` to the graph with
edges `(x, z)`, `(y, z)`, and `(z, v)` for all `v` that is reachable from both `x` and `y` in `Gₖ`.
Symmetrically, we add new vertices by checking the `HasInf` predicates. Note that the reachability
relation on `Gₖ` is preserved: for any two vertices `x`, `y` from `Gₖ₊₁`, there is a path from `x` to
`y` iff there is such a path in `Gₖ`.

Finally, let's denote `G'` as the union of all `Gₖ`. The carrier of our model is then the set of
strongly connected components in `G'`, and the relation `R` is defined as `C₁ R C₂` iff `C₂` is
reachable from `C₁`. For any two vertices `x` and `y` in `G'`, we define
`[x] ⊔ [y]` as `[z]` for some `z` for which `Sup(x, y, z)` holds, and similarly for `⊓`. One can
easily check that the definition is correct, and all facts from `T'` are satisfied.

### Boolean algebra
For Boolean algebras, there are 4 new types of facts, namely:
* `x = ⊤`
* `x = ⊥`
* `x = yᶜ`
* `x = y ⇨ z`

for some variables `x`, `y`, and `z`.
It is well known that checking if `φ=1` is provable in the theory of Boolean algebras for some term `φ` is equivalent to checking if (the natural translation of) `φ` is a classical tautology. This means that the decision problem from this theory is **coNP**-complete. One could implement a simple tactic for this using the following pipeline:
1. Use Stone's representation theorem to translate all facts from an arbitrary Boolean algebra `α` to Boolean algebra `Set β` for some `β`.
2. Finish the goal using the `set_tauto` tactic.

### Distributive lattice
The tactic for solving goals in this theory is the same as described above, with only the change that one needs Stone's representation theorem for distributive lattices.

Let me show that this decision problem is also **coNP**-complete by reducing the previous one to this.

Let `T` be some set of facts in Boolean algebras theory. We construct the set `T'` of facts in the theory of distributive lattices from `T` as follows:
* Add two fresh variables `b` and `t`, and replace all facts `x = ⊤` with `x = t` and all facts `x = ⊥` with `x = b`. Also add facts `x ≤ t` and `b ≤ x` for all variables `x`.
* Replace facts `x = yᶜ` with `x ⊔ y = t` and `x ⊓ y = b`.
* For facts `x = y ⇨ z`, introduce a new variable `u` and add three facts: `x = u ⊔ z`, `u ⊓ y = b`, `u ⊔ y = t` (here `u` has the meaning `yᶜ`).
* Leave other facts unchanged.

Suppose that `T` is satisfiable in the theory of Boolean algebra, i.e., there is a Boolean algebra `M` that satisfies `T`. Then the same algebra (viewed as a distributive lattice) satisfies `T'` if we interpret `t` and `b` as `⊤` and `⊥`, and `u` as `yᶜ` for each replacement for facts of the form `x = y ⇨ z` described above.

Suppose now that `T'` is satisfiable in the theory of distributive lattices, i.e., there is a distributive lattice `M` that satisfies `T'`. Let `N` be a sublattice of `M` generated by values of variables from `T'`. It is easy to see that `t` and `b` are the greatest and lowest elements in `N`. `N`, as any bounded distributive lattice, can be embedded into some Boolean algebra `B` (as a sublattice). Then `B` is a model of `T`:
* Each fact `x = ⊤` is satisfied because `N(x) = N(t) = ⊤` and then `B(x) = ⊤`. Similarly for `⊥`.
* Each fact `x = yᶜ` is satisfied because `N(x) ⊔ N(y) = ⊤` and `N(x) ⊓ N(y) = ⊥` (as `N` is a model of `T'`), and similar equalities are true for `B` as the embedding preserves lattice operations, least and greatest elements. These two equalities imply `B(x) = B(y)ᶜ` in Boolean algebras.
* Each fact `x = y ⇨ z` is equivalent to `x = yᶜ ⊔ z` or `x = u ⊔ z`, `u = yᶜ`.
From the previous we know that `B(u) = B(y)ᶜ`, and from properties of embedding, we obtain `B(x) = B(y)ᶜ ⊔ B(z)`, as required.
* All other facts from `T` are in `T'` too, so they are satisfied in `N`, and then in `B`.

This shows that the decision problem for Boolean algebras can be reduced to the decision problem for distributive lattices, implying that the latter is **coNP**-complete.

### `⊤` and `⊥`
If the existence of `⊤` and `⊥` is added to the theory, we add the edges `(x, ⊤)` and `(⊥, x)` for all vertices `x`, using `le_top`
and `bot_le`, respectively. One can easily check that it preserves the complexity and completeness of all algorithms.
