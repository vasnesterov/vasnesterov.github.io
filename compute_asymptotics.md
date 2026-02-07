# Introduction

This is a reference for the `compute_asymptotics` tactic implementation. I wrote it for reviewers to give full context on what's going on here. 
You can find the complete code [here](https://github.com/leanprover-community/mathlib4/pull/28291). 
If you have any questions or remarks, feel free to contact me on Zulip or open a PR or issue at [this repo](https://github.com/vasnesterov/vasnesterov.github.io/).

## High-level idea of the tactic

The purpose of the tactic is to prove asymptotic goals about numerical functions. For example:

```lean
import Mathlib.Tactic.ComputeAsymptotics.Main

open Real Filter Topology Asymptotics

example : Tendsto (fun (x : ℝ) ↦ (1 + 6 * x⁻¹) ^ (7 * x)) atTop (𝓝 (exp 42)) := by
  compute_asymptotics

example : (fun x ↦ x - 1 - log x) ~[𝓝[≠] 1] (fun x ↦ (x - 1) ^ 2 / 2) := by
  compute_asymptotics

-- It works with non-numerical parameters as well
example (a b : ℝ) (h : a < b) :
    (fun x ↦ (x + x * log x) ^ a) =O[atTop] (fun x ↦ (x / log x) ^ b) := by
  compute_asymptotics

example :
    (fun x ↦ log x) =o[𝓝[>] 0] (fun x ↦ Real.pi / (exp (Real.log 2 * x) - 1)) := by
  compute_asymptotics
```

It is possible to reduce the goals we care about to computing limits of functions `ℝ → ℝ` at
the filter `atTop`.

Tactic implementation consists of two big parts:

### Theory of multiseries

The main object of study is a **multiseries** — a generalization of asymptotic expansions. We use
them to approximate functions in some sense, but they are purely algebraic objects that we can
compute with directly.

We define multiseries and operations on them (`-`, `+`, `*`, `log`, `exp`, `inv`, powers, etc.). For
each operation we prove that it respects the "approximation" relation. For example, if `f` is approximated by
multiseries `F` and `g` by `G`, then `f + g` is approximated by `F + G`.

### Meta-code

To compute the limit of a function `f` (given as an `Expr`):

1. **Build a multiseries** `F` that approximates `f`: traverse the expression and replace function
   operations by the corresponding multiseries operations (e.g. `fun x ↦ (x + 1)^2` becomes
   `(id + const 1)^2`). At the same time we build proofs that `f` is approximated by `F` using the
   operation lemmas.
2. **Normalize and trim** `F`: simulate lazy evaluation to put `F` in normal form (head = `nil` or
   `cons exp coef tl`), then trim so that the leading coefficient is "nonzero" in a sense that
   allows extracting asymptotics.
3. **Leading term and limit**: read off the leading term,
   compute its limit, and conclude the same limit for `f`.

# Theory of multiseries

## Definition of multiseries (`MultiseriesExpansion` and `Multiseries`)

First of all, we need to define a *basis*. A basis is just a list of real functions.
```lean
abbrev Basis := List (ℝ → ℝ)
```

A multiseries in a basis `[b₁, ..., bₙ]` is a formal series made
from monomials `b₁ ^ e₁ * ... * bₙ ^ eₙ` where `e₁, ..., eₙ` are real numbers.

The initial definition of multiseries in Lean was the following:

```lean
def MultiseriesExpansion (basis : Basis) : Type :=
  match basis with
  | [] => ℝ
  | basis_hd :: basis_tl => Seq (ℝ × MultiseriesExpansion basis_tl) × (ℝ → ℝ)
```

We treat multivariate series in the basis `[b₁, ..., bₙ]` as a univariate series in the
variable `b₁` (`basis_hd`) with coefficients being multiseries in the
basis `[b₂, ..., bₙ]` (`basis_tl`). We represent such a series as a lazy list (`Seq`)
of pairs `(exp, coef)` where `exp` is the exponent of `b₁` and `coef` is the coefficient (a multiseries in `basis_tl`).
A multiseries in an empty basis is just a real number.

For example, the series `7 b₁² b₂⁴ + 5 b₁² b₂³ + 6 b₁` is represented as
`[(2, [(4, 7), (3, 5)]), (1, [(0, 6)])]`.

But it turns out we need to explicitly store a function attached to the multiseries (the function
it approximates). See [trimming] for more details.

So we use two types, `MultiseriesExpansion` and `Multiseries`, which we would like to define like this:

```lean
mutual

def Multiseries (basis_hd : ℝ → ℝ) (basis_tl : Basis) : Type := Seq (ℝ × MultiseriesExpansion basis_tl)

def MultiseriesExpansion (basis : Basis) : Type :=
  match basis with
  | [] => ℝ
  | basis_hd :: basis_tl => (Multiseries basis_hd basis_tl) × (ℝ → ℝ)

end
```

Using `mutual` to define types breaks some def-eqs, but luckily we can define `MultiseriesExpansion` and `Multiseries`
separately. Having both types is more convenient than having only `MultiseriesExpansion`, for two reasons:
* Most constructions (`Sorted`, `Trimmed`, `leadingExp`, etc.) don't refer to the function attached to the multiseries,
  so it's easier to state them for `Multiseries`.
* We can use the `Seq` API directly for `Multiseries`, but not for `MultiseriesExpansion`.

We call `nil` and `cons exp coef tl` the normal forms for `Multiseries`. For `MultiseriesExpansion` we
call `mk s f` the normal form, where `s` is a `Multiseries` and `f` is the real function.
An important step of the algorithm is *normalization*: we simulate lazy evaluations of multiseries
until we reach the normal form.

## `Sorted` predicate

`Sorted (ms : MultiseriesExpansion basis)` means that at each level of `ms` the exponents in the list are **strictly
decreasing**. This is defined as follows. First we define `MultiseriesExpansion.leadingExp` - the first exponent at `basis_hd`.
```lean
def Multiseries.leadingExp (s : Multiseries basis_hd basis_tl) : WithBot ℝ :=
  match s.head with
  | none => ⊥
  | some (exp, _) => exp

def MultiseriesExpansion.leadingExp (ms : MultiseriesExpansion (basis_hd :: basis_tl)) : WithBot ℝ :=
  ms.seq.leadingExp
```

Then we define `Sorted` as a predicate on `MultiseriesExpansion` and `Multiseries`:
```lean
/-- Auxiliary instance for order on pairs `(exp, coef)` used below to define `Sorted` in terms
of `Seq.Pairwise`. `(exp₁, coef₁) ≤ (exp₂, coef₂)` iff `exp₁ ≤ exp₂`. -/
scoped instance {basis} : Preorder (ℝ × MultiseriesExpansion basis) := Preorder.lift Prod.fst

inductive Sorted : {basis : Basis} → (MultiseriesExpansion basis) → Prop
| const (ms : MultiseriesExpansion []) : Sorted ms
| seq {hd} {tl} (ms : MultiseriesExpansion (hd :: tl))
    (h_coef : ∀ x ∈ ms.seq, x.2.Sorted)
    (h_Pairwise : Seq.Pairwise (· > ·) ms.seq) : ms.Sorted
```

Sortedness ensures that the first non-zero monomial is the dominant one, if the basis
is well-formed (see `WellFormedBasis`).

This definition doesn't refer to the function attached to the multiseries, so we mainly work with
a `Multiseries`-version of `Sorted`:
```lean
def Multiseries.Sorted {basis_hd basis_tl} (s : Multiseries basis_hd basis_tl) : Prop :=
  (mk s 0).Sorted (basis := basis_hd :: basis_tl)
```
and prove
```lean
theorem Sorted_iff_Seq_Sorted {ms : MultiseriesExpansion (basis_hd :: basis_tl)} :
    ms.Sorted ↔ Multiseries.Sorted ms.seq
```
to reduce `MultiseriesExpansion.Sorted` to `Multiseries.Sorted`.

In addition to constructors (`const`, `nil`, `cons`) and destructors we prove a coinduction principle:
```lean
theorem Sorted.coind {s : Multiseries basis_hd basis_tl}
    (motive : (ms : Multiseries basis_hd basis_tl) → Prop)
    (h_base : motive s)
    (h_step : ∀ exp coef tl, motive (.cons exp coef tl) →
        coef.Sorted ∧
        leadingExp tl < exp ∧
        motive tl) :
    s.Sorted
```
which we later use to prove that operations respect sortedness.

## Majorated predicate

To define `Approximates` predicate we need to introduce an auxiliary predicate.
`Majorated f g exp` for functions `f, g : ℝ → ℝ` and `exp : ℝ` means: for every
`exp' > exp`, `f =o[atTop] g ^ exp'`. So `f` is dominated by any power of `g` with
exponent greater than `exp`. Intuitively, this means that the right order of `f` in terms of
`g` is at most `g ^ exp`.

See `Approximates` for details on how `Majorated` is used.

## `Approximates` predicate

Let's define what it means for a multiseries to approximate a function.

A "true" definition of `Approximates` would be as a coinductive predicate:
```lean
coinductive Approximates {basis : Basis} (ms : MultiseriesExpansion basis) : Prop
| const (ms : MultiseriesExpansion []) : Approximates ms
| nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} (f : ℝ → ℝ) (hf : f =ᶠ[atTop] 0) :
  Approximates (mk (@nil basis_hd basis_tl) f)
| cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ} {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl}
    (h_coef : coef.Approximates) (h_maj : Majorated f basis_hd exp)
    (h_tl : (mk tl (f - basis_hd ^ exp * coef.toFun)).Approximates) :
  Approximates (mk (.cons exp coef tl) f)
```

Currently, Lean doesn't support this definition (but may do so soon), so we manually define it
as a greatest fixed point of the corresponding monotone map `Approximates.T`.

Let's break this definition down:
1. Multiseries in an empty basis always approximates its attached function (as it's just `fun _ ↦ ms.toReal`).
2. A nil multiseries approximates a function if it eventually equals zero.
3. `(exp, coef) :: tl` approximates a function `f` if
  `coef` approximates its attached function,
  `f` is majorated by `basis_hd ^ exp`,
  and the tail `tl` approximates `f - basis_hd ^ exp * coef.toFun` -- the remainder function.

## Well-formedness of basis

Bases we work with must be **well-formed**, which means:
1. Every function in `basis` tends to `atTop` at `atTop`.
2. The basis is ordered so that for any two distinct elements `f`, `g` with `g` later than `f`,
  we have `log ∘ g =o[atTop] log ∘ f`.

The last condition allows us to asymptotically compare monomials:
if `(α₁, ..., αₙ) < (β₁, ..., βₙ)` in the lexicographical order, and `basis = [b₁, ..., bₙ]`, then
`b₁ ^ α₁ * ... * bₙ ^ αₙ` is little-o of `b₁ ^ β₁ * ... * bₙ ^ βₙ`.

## `Trimmed` predicate

A multiseries is **Trimmed** if it's either nil, or its leading monomial is non-zero
(and therefore determines the asymptotics of the function).

Formally, it is defined as follows:
```lean
inductive IsZero : {basis : Basis} → MultiseriesExpansion basis → Prop
| const {c : MultiseriesExpansion []} (hc : c.toReal = 0) : IsZero c
| nil {basis_hd} {basis_tl} (f) : @IsZero (basis_hd :: basis_tl) (mk .nil f)

inductive Trimmed : {basis : Basis} → MultiseriesExpansion basis → Prop
| const {c : ℝ} : @Trimmed [] c
| nil {basis_hd} {basis_tl} {f} : @Trimmed (basis_hd :: basis_tl) (mk .nil f)
| cons {basis_hd} {basis_tl} {exp : ℝ} {coef : MultiseriesExpansion basis_tl}
  {tl : Multiseries basis_hd basis_tl} {f : ℝ → ℝ} (h_trimmed : coef.Trimmed)
  (h_ne_zero : ¬ IsZero coef) :
  @Trimmed (basis_hd :: basis_tl) (mk (.cons exp coef tl) f)
```

We need a multiseries to be trimmed for
1. determining the asymptotic of the function
2. substituting a multiseries into a power series

Sometimes we need to bring a multiseries to trimmed form. This is done on the meta-level by the
`trim` function.

## Basic monomials constructions

We define basic monomials constructions for multiseries:

* **const basis c**: multiseries representing the constant function `c`.
* **zero**, **one**: additive and multiplicative units.
* **monomial basis n**, **monomialRpow basis n r**: multiseries representing `basis[n]` and
  `basis[n] ^ r` respectively.

## Monomials and their limits

Let's compute the limit of a monomial. We define

```lean
structure Term where
  coef : ℝ
  exps : List ℝ
```

The monomial `⟨coef, exps⟩` is interpreted as the function `coef * basis[0]^exps[0] * basis[1]^exps[1] * ...`.

Assuming the basis is well-formed, computing the limit of a monomial is straightforward.

1. If the first non-zero exponent in `exps` is positive, the limit is `±∞` and the sign is
  determined by the sign of `coef`.
2. If the first non-zero exponent in `exps` is negative, the limit is `0`.
3. If all exponents are zero, the limit is `coef`.

We define predicates `FirstIsPos`, `FirstIsNeg`, `AllZero` on `exps` corresponding to the above cases.
On the meta-level we determine which one of these predicates holds and use the corresponding theorem
to get the limit.

## Leading term of a multiseries

To compute the asymptotic of a multiseries, we find its leading term.
`leadingTerm ms` for `ms : MultiseriesExpansion basis` is the `Term` at the "front" of the expansion: the list
of leading exponents at each level (`ms.exps`) and the real coefficient at the end (`ms.realCoef`).

We prove `IsEquivalent_leadingTerm`: `ms.toFun ~[atTop] ms.leadingTerm.toFun basis` which means that
the limit of `ms.toFun` is the same as the limit of `ms.leadingTerm.toFun`. We can compute the
latter as described above.
The `log` and `exp` operations also require some preconditions on the leading term.


## Corecursion for `Multiseries`

Operations on multiseries are defined by corecursion. As well as recursion, corecursion
justifies some self-referential definitions. It may be primitive or non-primitive.

### Primitive corecursion

Let's first look at a simple case of the `Stream` type.
Primitive corecursion justifies definitions of the form

```lean
def foo (b : β) : Stream α := hd b :: foo (newArg b)
```
where `hd` and `newArg` are arbitrary functions. In Lean it's done as follows:
```lean
def foo (b : β) : Stream α := corec hd newArg b

-- prove that the "true" definition holds
theorem foo_eq (b : β) : foo b = hd b :: foo (newArg b) := Stream'.corec_eq
```

So, primitive corecursion can be directly expressed by `corec`.

Because `Seq` may be empty, its `corec` is a little more complicated.
```lean
def (f : β → Option (α × β)) (b : β) : Seq α
```
So instead of `⟨hd, newArg⟩ : β → (α × β)` we now have `f : β → Option (α × β)` and
`none` means empty list.

This is directly translated for `Multiseries`:
```lean
def Multiseries.corec (f : β → Option (ℝ × MultiseriesExpansion basis_tl × β)) (b : β) : Multiseries basis_hd basis_tl
```

Using primitive corecursion we define negation and addition of multiseries. But it's not enough
to define multiplication and `powser`.

### Non-primitive corecursion

To define multiplication and `powser` we need to slightly extend the class of allowed
corecursive definitions. Again, starting with `Stream`, we would like to allow definitions of the form
```lean
def foo (b : β) : Stream α := hd b :: op (foo (newArg b))
```

where `op : Stream α → Stream α` is a *friendly* operation. Friendly means that
the n-th prefix of `op s` depends only on the n-th prefix of `s`.

Such definitions cannot be expressed by `corec` directly, so we need to develop some theory to
justify them.

We prove that for any `hd`, `newArg`, and `op` there exists a function `foo` that satisfies
the above equation, and then use `Exists.choose` to extract it into `Seq.gcorec`.

We also prove `FriendOperation.coind` - a coinduction principle for proving `FriendOperation`, which
we later use to prove that addition and multiplication are friendly operations.

## Basic operations on multiseries: `mulConst` and unary minus

The first operations we define are multiplication by a constant and negation:
```lean
def mulConst {basis : Basis} (c : ℝ) (ms : MultiseriesExpansion basis) : MultiseriesExpansion basis :=
  match basis with
  | [] => ofReal (c * ms.toReal)
  | List.cons _ _ =>
    mk (ms.seq.map id (fun coef => coef.mulConst c)) (c • ms.toFun)

def neg {basis : Basis} (ms : MultiseriesExpansion basis) : MultiseriesExpansion basis :=
  ms.mulConst (-1)
```
This is easy to define via `Multiseries.map`.

As with other operations, we provide `Multiseries`-versions:
```lean
def Multiseries.mulConst {basis_hd basis_tl} (c : ℝ) (ms : Multiseries basis_hd basis_tl) :
    Multiseries basis_hd basis_tl :=
  ms.map id (fun coef => coef.mulConst c)

def Multiseries.neg {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl) : Multiseries basis_hd basis_tl :=
  ms.mulConst (-1)
```

Then we prove
1. "Structural" lemmas for `Multiseries`-versions.
2. `Multiseries.mulConst_Sorted`: `Multiseries.mulConst` respects sortedness
3. `MultiseriesExpansion.mulConst_Approximates`: `ms.mulConst c` approximates the function attached to it
  (`c • ms.toFun`)

## Addition of multiseries

The next operation we define is addition. A "true" definition would be corecursive:
```lean
mutual

def MultiseriesExpansion.add (X Y : MultiseriesExpansion basis) : MultiseriesExpansion basis :=
  match basis with
  | [] => ofReal (X.toReal + Y.toReal)
  | basis_hd :: basis_tl => mk (Multiseries.add X.seq Y.seq) (X.toFun + Y.toFun)

def Multiseries.add (X Y : Multiseries basis_hd basis_tl) : Multiseries basis_hd basis_tl :=
  match X, Y with
  | nil, _ => Y
  | _, nil => X
  | (X_exp, X_coef) :: X_tl, (Y_exp, Y_coef) :: Y_tl =>
    if Y_exp < X_exp then
      (X_exp, X_coef) :: (X_tl.add Y)
    else if X_exp < Y_exp then
      (Y_exp, Y_coef) :: (X.add Y_tl)
    else -- X_exp = Y_exp
      (X_exp, X_coef.add Y_coef) :: (X_tl.add Y_tl)

end
```

Lean doesn't support corecursive definitions, so we need to manually rewrite the definition using
the corecursion combinator `Multiseries.corec`, and then prove the above equation as a theorem: `Multiseries.add_unfold`.

We then prove
1. "Structural" lemmas for `Multiseries.add`
2. Algebraic properties: multiseries form an `AddCommMonoid`. That allows us to use `abel` tactic in our proofs.
3. `Multiseries.add_Sorted`: `Multiseries.add` respects sortedness
4. `MultiseriesExpansion.add_Approximates`: `ms.add X Y` approximates the function attached to it
  (`X.toFun + Y.toFun`)
5. That `X + ·` (with constant `X`) is a friend operation for `Multiseries`. That allows us to define `Multiseries.mul` using
  non-primitive corecursion.
6. A coinduction principle for `Sorted`:
  ```lean
  theorem Multiseries.Sorted.add_coind {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : Multiseries basis_hd basis_tl}
    (motive : Multiseries basis_hd basis_tl → Prop) (h_base : motive ms)
    (h_step :
      ∀ (exp : ℝ) (coef : MultiseriesExpansion basis_tl) (tl : Multiseries basis_hd basis_tl),
        motive (.cons exp coef tl) → coef.Sorted ∧ tl.leadingExp < ↑exp ∧
        ∃ A B, tl = A + B ∧ A.Sorted ∧ motive B) :
    ms.Sorted
  ```
  (cf. `Sorted.coind`)

7. A coinduction principle for `Approximates`:
  ```lean
  theorem Approximates.add_coind {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : MultiseriesExpansion (basis_hd :: basis_tl)}
    (motive : MultiseriesExpansion (basis_hd :: basis_tl) → Prop) (h_base : motive ms)
    (h_step :
      ∀ (ms : MultiseriesExpansion (basis_hd :: basis_tl)),
        motive ms →
        ms.seq = .nil ∧ ms.toFun =ᶠ[atTop] 0 ∨
        ∃ exp coef tl,
          ms.seq = .cons exp coef tl ∧ coef.Approximates ∧ majorated ms.toFun basis_hd exp ∧
          ∃ (A : MultiseriesExpansion (basis_hd :: basis_tl)) (B : Multiseries basis_hd basis_tl),
          tl = A.seq + B ∧ A.Approximates ∧
          motive (mk (basis_hd := basis_hd) B (ms.toFun - basis_hd ^ exp * coef.toFun - A.toFun))) :
    ms.Approximates
  ```
  (cf. `Approximates.coind`)

## Multiplication of multiseries

Multiplication is defined by mutual recursion with "multiplication by a monomial" operation:
```lean
mutual

  /-- `Multiseries`-part of `MultiseriesExpansion.mul`. -/
  noncomputable def Multiseries.mul {basis_hd : ℝ → ℝ} {basis_tl : Basis}
      (X Y : Multiseries basis_hd basis_tl) : Multiseries basis_hd basis_tl :=
    match X, Y with
    | nil, _ => .nil
    | _, nil => .nil
    | cons X_exp X_coef X_tl, cons Y_exp Y_coef Y_tl =>
      cons (X_exp + Y_exp) (X_coef.mul Y_coef) ((Multiseries.mulMonomial X_tl Y_coef Y_exp).add Y_tl)

  /-- `Multiseries`-part of `MultiseriesExpansion.mulMonomial`. -/
  noncomputable def Multiseries.mulMonomial {basis_hd} {basis_tl} (B : Multiseries basis_hd basis_tl)
      (M_coef : MultiseriesExpansion basis_tl) (M_exp : ℝ) : Multiseries basis_hd basis_tl :=
    B.map (fun exp => exp + M_exp) (fun coef => coef.mul M_coef)

  /-- Multiplication for multiseries. -/
  noncomputable def mul {basis : Basis} (X Y : MultiseriesExpansion basis) : MultiseriesExpansion basis :=
    match basis with
    | [] => ofReal (X.toReal * Y.toReal)
    | List.cons basis_hd basis_tl =>
      mk (Multiseries.mul X.seq Y.seq) (X.toFun * Y.toFun)

  /-- Multiplication by monomial, i.e. `B * basis_hd ^ M_exp * M_coef`. -/
  noncomputable def mulMonomial {basis_hd} {basis_tl} (B : MultiseriesExpansion (basis_hd :: basis_tl))
      (M_coef : MultiseriesExpansion basis_tl) (M_exp : ℝ) : MultiseriesExpansion (basis_hd :: basis_tl) :=
    mk (Multiseries.mulMonomial B.seq M_coef M_exp) (B.toFun * basis_hd ^ M_exp * M_coef.toFun)

end
```

Again, we can't define `Multiseries.mul` directly using corecursion, we need to manually rewrite
the definition using `Multiseries.gcorec` with `Multiseries.add` as the friend:
```lean
noncomputable def Multiseries.mul {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (X Y : Multiseries basis_hd basis_tl) : Multiseries basis_hd basis_tl :=
  match X.destruct with
  | none => .nil
  | some (X_exp, X_coef, X_tl) =>
    let T := Multiseries basis_hd basis_tl
    let g : T → Option (ℝ × MultiseriesExpansion basis_tl × Multiseries basis_hd basis_tl × T) := fun Y =>
      match Y.destruct with
      | none => none
      | some (Y_exp, Y_coef, Y_tl) =>
        some (X_exp + Y_exp, X_coef.mul Y_coef, Multiseries.mulMonomial X_tl Y_coef Y_exp, Y_tl)
    Multiseries.gcorec g Multiseries.add Y
```

As multiplication is defined by non-primitive corecursion with addition as the friend, we heavily
rely on coinduction principles for `Sorted` and `Approximates` with addition in the tail in proofs.

Then we prove
1. "Structural" lemmas: `Multiseries.mul_cons_cons`, `Multiseries.mul_nil`, `Multiseries.mulMonomial_cons`, etc.
2. Algebraic properties: distributivity and associativity
3. `Multiseries.mul_Sorted`: multiplication preserves sortedness
4. `MultiseriesExpansion.mul_Approximates`: `X.mul Y` approximates `X.toFun * Y.toFun`
5. That `X.mul ·` is a friend operation for `Multiseries`. This allows us to define `Multiseries.powser`
   using non-primitive corecursion.
6. Coinduction principles for `Sorted` and `Approximates` with multiplication in the tail:
  `Multiseries.Sorted.mul_coind` and `Approximates.mul_coind`

## `LazySeries` and `powser` operation

Let's define substitution of a multiseries into a power series. We use
```lean
abbrev LazySeries := Seq ℝ
```
to represent (univariate) formal power series as a sequence of coefficients.

We provide the following API for `LazySeries`:
1. `toFormalMultilinearSeries`: converts a lazy series to a formal multilinear series
2. `toFun`: the sum of the series
3. `Convergent`: a predicate stating that the series converges on some non-trivial ball

Then we define `powser` operation:
```lean
noncomputable def Multiseries.powser (s : LazySeries) {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (ms : Multiseries basis_hd basis_tl) : Multiseries basis_hd basis_tl :=
  match s with
  | nil => .nil
  | cons c cs =>
    cons 0 (MultiseriesExpansion.const _ c) (ms.mul (Multiseries.powser cs ms))

noncomputable def MultiseriesExpansion.powser (s : LazySeries) {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (ms : MultiseriesExpansion (basis_hd :: basis_tl)) : MultiseriesExpansion (basis_hd :: basis_tl) :=
  mk (Multiseries.powser s ms.seq) (s.toFun ∘ ms.toFun)
```

Again, we can't define `Multiseries.powser` directly using corecursion, we need to manually rewrite
the definition using `Multiseries.gcorec` with `Multiseries.mul` as the friend:
```lean
noncomputable def Multiseries.powser (s : LazySeries) {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (ms : Multiseries basis_hd basis_tl) : Multiseries basis_hd basis_tl :=
  let T := LazySeries
  let g : T → Option (ℝ × MultiseriesExpansion basis_tl × Multiseries basis_hd basis_tl × T) := fun s =>
    match s.destruct with
    | none => none
    | some (c, cs) =>
      some (0, MultiseriesExpansion.const _ c, ms, cs)
  Multiseries.gcorec g Multiseries.mul s
```


As `powser` is defined by non-primitive corecursion with multiplication as the friend, we heavily
rely on coinduction principles for `Sorted` and `Approximates` with multiplication in the tail in proofs.

For this operation to make sense, in some theorems we require `ms.leadingExp < 0` so
that `ms.toFun` tends to 0 at `atTop`

Then we prove
1. "Structural" lemmas: `Multiseries.powser_nil`, `Multiseries.powser_cons`
2. `powser_Sorted`: when `ms.Sorted` and `ms.leadingExp < 0`, the result is Sorted
3. `powser_Approximates`: when `s.Convergent`, and `ms.leadingExp < 0`,
   `powser s ms` approximates `s.toFun ∘ ms.toFun`

## Inversion and powers with constant exponent

Inversion and powers with constant exponent are direct applications of `powser`. For both operations,
we define the corresponding series, `invSeries := [1, -1, 1, -1, ...]` and
`powSeries a := [1, a, a * (a - 1) / 2, a * (a - 1) * (a - 2) / 6, ...]`. Then we prove it converges
and use a theorem from Mathlib to prove that its `toFun` is the desired function
(`(1 + x)⁻¹` or `(1 + x) ^ a`). We define `MultiseriesExpansion.inv` as follows:

```lean
mutual

noncomputable def Multiseries.inv {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl) :
    Multiseries basis_hd basis_tl :=
  match ms.destruct with
  | none => .nil
  | some (exp, coef, tl) => Multiseries.mulMonomial
    (Multiseries.powser invSeries (tl.mulMonomial coef.inv (-exp))) coef.inv (-exp)

noncomputable def inv {basis : Basis} (ms : MultiseriesExpansion basis) : MultiseriesExpansion basis :=
  match basis with
  | [] => ofReal <| ms.toReal⁻¹
  | List.cons _ _ =>
    mk (Multiseries.inv ms.seq) ms.toFun⁻¹

end
```
(and similar for `MultiseriesExpansion.pow`)

The idea here is to if `f = basis_hd ^ exp * coef.toFun + tl.toFun` where `tl.leadingExp < exp`, then
`f⁻¹ = basis_hd ^ (-exp) * (coef.toFun)⁻¹ * (1 + basis_hd ^ (-exp) * (coef.toFun)⁻¹ * tl.toFun)⁻¹ = basis_hd ^ (-exp) * coef.inv.toFun * (1 - basis_hd ^ (-exp) * coef.inv.toFun * tl.neg.toFun)⁻¹`,
and the leading exponent of `basis_hd ^ (-exp) * coef.inv.toFun * tl.neg.toFun` is negative, so we can use `powser` for the last term.

For this to make sense, we need `coef.toFun` to be non-zero. So before applying `inv` (or `pow`) we
trim the multiseries.

Using theorems about other operations, we prove that `inv` and `pow` respect sortedness and approximation.

As `Real.rpow` behaves well only for non-negative arguments, we require an additional precondition
`ms.leadingTerm.coef > 0` in `pow_Approximates`.

There are also versions `MultiseriesExpansion.npow` and `MultiseriesExpansion.zpow` for natural and integer exponents that don't
require this precondition.

## `LogBasis` structure

Operations we described above do not change the basis. Logarithm and exponential, however, do.

Along with the basis, we store a **log-basis**. If `basis = [b₁, b₂, ..., bₙ]`,
then log-basis is a list of multiseries approximations of log b₁, ..., log bₙ₋₁, where
`log bᵢ` is expanded in the basis `[bᵢ₊₁, ..., bₙ]`.

## Basis change

During the algorithm we maintain a basis we work with.
Sometimes we need to insert a new function into the basis. For this we use
1. `MultiseriesExpansion.extendBasisEnd` lifts a multiseries from the basis `[b₁, b₂, ..., bₙ]` to the
  basis `[b₁, b₂, ..., bₙ, f]` with a new function `f`.
2. `MultiseriesExpansion.extendBasisMiddle` does the same, but `f` is inserted somewhere except the last position.
3. `LogBasis.extendBasisEnd` and `LogBasis.extendBasisMiddle` do the same for `LogBasis`.
4. Sometimes we have a multiseries in some basis `bs` and need to lift it to a larger basis `bs'`.
  For example this happens when we deal with binary operations: when we need to compute an
  expansion of `f + g`, we compute an expansion `F` of `f` in some basis `bs`, then an expansion
  `G` of `g` in some basis `bs'` (`bs <+ bs'`) and then we must lift `F` to `bs'`. This is done by
  `MultiseriesExpansion.updateBasis` that takes a `BasisExtension` as an argument.

`BasisExtension` is a structure that represents a change of basis.
```lean
inductive BasisExtension : Basis → Type
| nil : BasisExtension []
| keep (basis_hd : ℝ → ℝ) {basis_tl : Basis} (ex : BasisExtension basis_tl) :
  BasisExtension (basis_hd :: basis_tl)
| insert {basis : Basis} (f : ℝ → ℝ) (ex : BasisExtension basis) : BasisExtension basis
```
So `ex : BasisExtension bs` contains data describing how to construct a basis `bs'` from `bs`.

When we need to lift `F` to `bs'`, in the example above, we find (on the meta-level)
the `BasisExtension` that converts `bs` to `bs'` and substitute it into `MultiseriesExpansion.updateBasis`.

## Logarithm of a multiseries

All operations above are completely defined inside the theory. Logarithm and exponential,
are partially defined on the meta-level.

We again use power series for the logarithm: `logSeries := [0, 1, -1/2, 1/3, ...]`
(an expansion of `log (1 + x)`).

Let's take a look at the `MultiseriesExpansion.log` definition:
```lean
mutual

noncomputable def Multiseries.log {basis_hd basis_tl}
    (logBasis : LogBasis (basis_hd :: basis_tl))
    (ms : Multiseries basis_hd basis_tl) :
    Multiseries basis_hd basis_tl :=
  match ms.destruct with
  | none => .nil
  | some (exp, coef, tl) =>
    match basis_tl with
    | [] => (Multiseries.const _ _ (Real.log coef.toReal)) +
        (tl.mulConst coef.toReal⁻¹).powser logSeries -- here exp = 0 by assumption
    | List.cons _ _ =>
      match logBasis with
      | .cons _ _ _ logBasis_tl log_hd =>
        (.cons 0 (log logBasis_tl coef + log_hd.mulConst exp) .nil) +
          (tl.mulMonomial coef.inv (-exp)).powser logSeries

noncomputable def log {basis : Basis}
    (logBasis : LogBasis basis)
    (ms : MultiseriesExpansion basis) :
    MultiseriesExpansion basis :=
  match basis with
  | [] => Real.log ms
  | List.cons basis_hd basis_tl => mk (Multiseries.log logBasis ms.seq) (Real.log ∘ ms.toFun)

end
```

This definition works when the last exponent of the leading term of `ms` is 0.
1. If `basis_tl = []` (i.e. `basis = [basis_hd]`), then
  `log f = log (basis_hd ^ 0 * coef.toFun + tl.toFun) = Real.log coef.toReal + log (1 + coef.toReal⁻¹ * tl.toFun)`.
2. If `basis_tl ≠ []`, then
  `log f = log coef.toFun + exp * log basis_hd + log (1 + basis_hd ^ (-exp) * coef.inv.toFun * tl.toFun)`.
  The only difference is the second term, but since `basis_tl ≠ []`, we can extract an expansion of `log basis_hd` from log-basis.

On the meta-level, when asked to compute an expansion of `log f`, we compute an expansion `F` of `f`,
trim it and then check if the last exponent of the leading term is 0. If it is, we can directly use
`MultiseriesExpansion.log`, otherwise we push `log ∘ basis.getLast` into the basis before applying `MultiseriesExpansion.log`.

## Exponential of a multiseries

Suppose we have an expansion `F` of a function `f` and need to compute an expansion for `exp ∘ f`.
The case `F = []` is trivial, let's focus on the case `F = (exp, coef) :: tl`.
We inspect the leading term of `F`. There are two possibilities.

### `¬ FirstIsPos F.exps`
This case can be handled completely inside the theory.

As above, we use a power series, now for `exp`: `expSeries := [1, 1/2, 1/6, 1/24, ...]`.

Then we can define
```lean
mutual

noncomputable def Multiseries.exp {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (ms : Multiseries basis_hd basis_tl) : Multiseries basis_hd basis_tl :=
  match ms.destruct with
  | .none => Multiseries.one
  | .some (exp, coef, tl) =>
    if exp < 0 then
      ms.powser expSeries
    else -- we assume that exp = 0
      (tl.powser expSeries).mulMonomial coef.exp 0

noncomputable def exp {basis : Basis} (ms : MultiseriesExpansion basis) :
    MultiseriesExpansion basis :=
  match basis with
  | [] => ofReal <| Real.exp ms.toReal
  | List.cons _ _ =>
    mk (Multiseries.exp ms.seq) (Real.exp ∘ ms.toFun)

end
```

The idea is that if `exp < 0` then `f` tends to zero and we may use `powser` with `expSeries`, and if `exp = 0` then `exp (f x) = exp (coef.toFun x + tl.toFun x) = exp (coef.toFun x) + exp (tl.toFun x)`. The first term is handled by recursion on `basis`, and the second one by the previous
construction, because `tl.leadingExp < F.leadingExp = 0`.

### `FirstIsPos F.exps`

This case is more complicated and might require basis change. We proceed as follows:
1. Go through the log-basis and compare (asymptotically) its elements with `F`. There are two possibilities: either `F ~ c • logBasis[i]` for some `c : ℝ` and `i`, or `F` can be inserted into
the log-basis at some position, i.e. we can split `logBasis = left ++ right` so that all elements of `right` are little-o of `F` and `F` is little-o of all elements of `left`.
2. If `F ~ c • logBasis[i]`, then 
```
exp (f x) = exp (c * logBasis[i] x) * exp (f - c • logBasis[i]) = (basis[i] x) ^ c * exp (f - c • logBasis[i])
```
and we recursively handle `exp (f - c • logBasis[i])` which is asymptotically strictly smaller (little-o) than `f`.
3. Otherwise, we update our basis. Let's denote by `i` the position of the first non-zero (and thus positive) exponent in `F.exps` and by `j` the length of `left`. The last element of `left` approximates `log ∘ basis[j]` in the basis `basis[j + 1:]`, so if we lift `left[j-1]` to the basis
`basis` it would have at least the first `j` exponents equal to zero. Therefore, `F = o(left[j-1])` implies `i > j`, i.e. the first `j` exponents of `F` are zero.
4. We extract `G` -- a "coefficient at depth `j`" of `F`. `G` is a multiseries in the basis `basis[j + 1:]` and `F ~ G` as functions. Assume `G` tends to `+∞`, the case of `-∞` is similar. We insert `G` into the log-basis between `left` and `right`, and `exp ∘ G` into the basis at the corresponding position. It's easy to see that all basis and log-basis invariants are preserved. Then we can return to step 2 as `F ~ G = newLogBasis[j]`. 

# Meta-level

## Comparison of real numbers

Along the way we need to compare real numbers. This is well-known to be undecidable, so we rely on
Mathlib's tactics for that purpose. In `CompareReal.lean` we define
```lean
inductive CompareResult (x : Q(Real))
| pos (pf : Q(0 < $x))
| neg (pf : Q($x < 0))
| zero (pf : Q($x = 0))
```

and then `compareReal (x : Q(ℝ)) : TacticM (CompareResult x)` that takes an expression of
real number and returns a `CompareResult` with a proof. So far, we use a combination of `norm_num`,
`linarith`, `positivity`, `field_simp`, `ring_nf` in `compareReal`, but this can be easily replaced
with any other tactic.

If `compareReal` fails, we throw an error like "Cannot compare real number `x` with zero.
You can use a `have` statement to provide the sign of the expression."

## Normalization

To extract the head of a multiseries we *normalize* it by simulating its lazy evaluation.
This is done by `normalizeMultiseriesExpansion`. It takes `ms : Q(MultiseriesExpansion basis)` and returns `ms'` that is normalized
along with a proof of `ms' = ms`. First, it computes `ms.toFun` -- this is easily done recursively
by applying theorems `MultiseriesExpansion.add_toFun`, etc. Then it computes `ms.seq` as
a `Q(Multiseries basis_hd basis_tl)` by applying theorems `MultiseriesExpansion.add_seq`, etc. So it basically
replaces all `MultiseriesExpansion` operations by `Multiseries` operations. Then it normalizes the result in
`normalizeMultiseries`.

It simulates the lazy evaluation of multiseries. For example to normalize `Multiseries.add F G` it
normalizes `F` and `G`, compares their leading exponents and decides which of the branches
of `add_unfold` holds and applies the corresponding theorem, e.g. `cons_add_cons_right` for the case
`F = (F_exp, F_coef) :: F_tl` and `G = (G_exp, G_coef) :: G_tl` and `F_exp < G_exp`.

## Eventual zeroness oracle

Sometimes we end up with a multiseries that approximates a zero function, but infinite.
For example, `(1 + x)⁻¹ - (1 + x)⁻¹` will be expanded as `[(0, 0), (-1, 0), (-2, 0), ...]`.
Such a multiseries cannot be trimmed in finite number of steps. To handle this case we use
an *eventual zeroness oracle*: some tactic that tries to prove that a function is eventually zero.
Then we can replace the infinite multiseries by `nil`.

So far, we use a very simple oracle: it reduces `f =ᶠ[atTop] 0` to `∀ x, f x = 0` and
then applies the `simp` and `field` tactics to the goal.

## Trimming

We call an expression `ms : Q(MultiseriesExpansion basis)` *trimmed* if it satisfies `MultiseriesExpansion.Trimmed ms` and
`ms` is in the normal form on all levels, i.e. it's either `nil`, or `cons (exp, coef) tl` where
`coef` is also `cons`, and so on. This allows to directly extract the leading term and determine
the asymptotic of the function. Sometimes it's enough to partially trim a multiseries -- normalize
it not at all levels but only up to some depth where it's clear that the first non-zero exponent
is negative. That would mean that the function tends to zero.

To trim a multiseries, we
1. Normalize it
2. If it's `nil` we're done. If it's `cons exp coef tl`, we trim `coef`.
3. If trimmed `coef` is zero (`0` or `nil`), we erase it and try to trim `tl`. Otherwise, we're done.

This process is implemented in `trimWithoutOracle`. We can't guarantee that it will terminate,
so after a certain number of steps we stop and try to use the eventual zeroness oracle to prove that
the attached function is eventually zero and return `nil`.

This is why we need to explicitly store the function `MultiseriesExpansion` approximates.

## Final algorithm

To conclude, to compute the limit of a function `f` at `atTop`, we
1. Compute an expansion `F` of `f` using the function `createMS`. We prove `F.toFun = f`,
`F.Sorted`, and `F.Approximates`.
2. Trim `F`, obtaining `F'` and a proof of `F'.toFun = f`, `F'.Sorted`, and `F'.Approximates`.
3. Extract the leading term of the trimmed `F` and prove one of the cases of `FirstIsPos` or `FirstIsNeg` or `AllZero` for it.
4. Use all proofs above to find and prove the limit of `f` at `atTop`.

# Miscellaneous

## Different asymptotic goals

Different "asymptotic goals" can be reduced to computing limits.

Different source filters are handled by a change of variable, for example
```lean
theorem tendsto_nhdsGT_of_tendsto_atTop (h : Tendsto (fun x ↦ f (c + x⁻¹)) atTop l) :
    Tendsto f (𝓝[>] c) l
```
is used to reduce the goal of the form `Tendsto f (𝓝[>] c) l` to the form `Tendsto f atTop l`.

Goals involving O-notation are handled similarly. For example for `IsBigO` we use
```lean
theorem isBigO_of_div_tendsto_atTop {f g : ℝ → ℝ} {l : Filter ℝ}
    (h : Tendsto (fun x ↦ g x / f x) l atTop) :
    f =O[l] g
```

## Different domains and codomains

TODO
