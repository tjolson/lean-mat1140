/- 
# MAT1140 Strukturer og argumenter - Høst 2021 Oblig 1, formalized in Lean (with solutions)
Comments and suggestions for improvement are welcome at torgero@math.uio.no 

Useful resource: 
- https://leanprover-community.github.io/mathlib_docs/data/set/basic.html

-/

import tactic
import data.set
open set function

section oppgaver_1_2

/-
Already in the first problem we see a difference between the set theory we use in everyday mathematics 
and a type theory that proof assistants like Lean use. Here all our sets are really *subsets* of
some specified *type*.  Whereas in set theory sets can contain vastly different objects (the union of 
*any* two sets is a set), all of the "sets" in Lean are made of *terms* of the same type.
-/
variable (U : Type) -- fix an arbitrary type our sets for our sets to live in
variables (A B : set U)

/-Oppgave 1.i-/
/-Note you can just use `library_search` to resolve this one and the next. The result however 
`exact inter_eq_left_iff_subset` invokes the very same statement we are trying and should thus be 
avoided.-/
example (A B : set U) : A ∩ B = A ↔ A ⊆ B :=
begin
  split, 
  { intro h,
    rw ← h,
    exact inter_subset_right A B, },
  intro h,
  ext,
  exact ⟨(λg, g.1), (λg, and.intro g (h g))⟩,
end

/-Oppgave 1.ii-/
/-Again this exercise is already in the mathlib as `union_eq_left_iff_subset`.-/
example (A B : set U) : A ∪ B = A ↔ B ⊆ A :=
begin
  split,
  { intro h,
    rw ← h,
    exact subset_union_right A B, },
  intro h,
  rw subset.antisymm_iff,
  split,
  { intros x g,
    cases g,
    exact g,
    exact h g, },
  exact subset_union_left A B,
end

/-Oppgave 2.i-/
/-In 1, A and B were arbitrary sets, here they were meant to be arbitrary subsets of some set U. We
could have simulated this by declaring a new type α and letting A, B and U be of type `set α` and
introducing hypotheses of type `A ⊆ U` and `B ⊆ U`, but the logic behind a solution would be the same 
and we can still access U as a "set" with `univ`. One downside is that we can no longer define the map 
Φ in the problem with codomain 𝒫(A) × 𝒫(B), since functions (avbildninger) in Lean always go between
types and we still want to think of the elements of 𝒫(A) as subsets of A (which are subsets of U). 
Without Φ, I modified the problem using what surjectivity and injectivity would mean in context. -/
example : (∀ (C D : set U), C ⊆ A ∧ D ⊆ B → ∃ (V : set U), (C, D) =  (V ∩ A, V ∩ B)) → (A ∩ B = ∅) :=
begin
  intro h,
  specialize h ∅ (A ∩ B), 
  have g := h (and.intro (empty_subset A) (inter_subset_right A B)),
  cases g with V hv,
  simp at hv,
  apply eq_empty_of_subset_empty,
  calc A ∩ B  ⊆ A ∩ (V ∩ B) : by exact (λx, (λh, and.intro h.1 (eq.subset hv.2 h)))
  ...         ⊆ V ∩ A : (λx, (λh, and.intro h.2.1 h.1))
  ...         ⊆ ∅ : (eq.symm (hv.1)).subset,
end

/-Oppgave 2.ii-/
/-It may be useful to recall that `simp` will change goals or hypotheses (X,Y) = (X',Y') and return 
what this means for the components: X = X' ∧ Y = Y'.-/
example : (A ∩ B = ∅) → (∀ (C D : set U), C ⊆ A ∧ D ⊆ B → ∃ (V : set U), (C, D) =  (V ∩ A, V ∩ B)) :=
begin
  rintros ne C D ⟨CA, DB⟩,
  use (C ∪ D),
  simp,
  repeat {rw union_inter_distrib_right},
  have e : D ∩ A = ∅ ∧ C ∩ B = ∅,
  { repeat {rw ← subset_empty_iff},
    repeat {rw ← ne}, --two repeats?
    rw inter_comm,
  exact ⟨inter_subset_inter_right A DB, inter_subset_inter_left B CA⟩, },
  rw [e.1, e.2, union_empty, empty_union],
  exact ⟨eq.symm (inter_eq_left_iff_subset.mpr CA), eq.symm (inter_eq_left_iff_subset.mpr DB)⟩,
end

/-Oppgave 2.iii -/
example : (∀ (V W : set U), (V ∩ A, V ∩ B) = (W ∩ A, W ∩ B) → V = W) → (univ = A ∪ B) :=
begin
  intro h,
  specialize h univ (A ∪ B),
  simp at h,
  exact (h union_inter_cancel_left.symm union_inter_cancel_right.symm),
end

/-Oppgave 2.iv -/
example : (univ = A ∪ B) → (∀ (V W : set U), (V ∩ A, V ∩ B) = (W ∩ A, W ∩ B) → V = W) :=
begin
  intros h V W g,
  simp at g,
  have e : (V ∩ A) ∪ (V ∩ B) = (W ∩ A) ∪ (W ∩ B) := by rw [g.1, g.2],
  repeat {rw ← inter_union_distrib_left at e},
  repeat {rw ← h at e},
  repeat {rwa inter_univ at e},
end
end oppgaver_1_2


section oppgave_3
open classical

variables (A B C : Type)
variable (f : A → B)
variable (g : A → C)
/-Again for simplicity I've slightly altered the following exercises. As stated above, the domain and
codomain of a function in Lean must be types. Declaring A, B and C as arbitrary types instead of 
subsets in some α lets us treat them the way we would in the original problem. -/

/-Oppgave 3.i -/
example (u : B → C) (c : g = u ∘ f) : ∀ (x x' : A), f x = f x' → g x = g x' :=
begin
  intros x x' h,
  rw c,
  simp,
  rw h,
end

/-Oppgave 3.ii -/
/-Here we see a less trivial difference in doing mathemetics on paper and in a computer. Lean would
seem to prefer functions being defined explicitly. It does manage, though I'm not quite yet sure how
it works. Note also that in this problem and 4.ii we have to invoke choice. -/
variable (c : C) -- using to insist to Lean that C is nonempty, as in the problem.
include c
local attribute [instance] prop_decidable
example (t : ∀ (x x' : A), f x = f x' → g x = g x') : ∃ u : B → C, g = u ∘ f :=
begin
  let u : B → C,
  { intro b,
    by_cases (∃ (a : A), f a  = b),
    { choose a ha using h,
      exact g a, },
    exact c, },
  use u,
  ext,
  have h1 : ∃ (a : A), f a = f x := by use x, 
  have h2 : (u ∘ f) x  = g (some h1) := dif_pos h1,
  rw h2,
  apply t,
  symmetry,
  apply some_spec h1,
end
end oppgave_3

section oppgave_4
open classical

variables (A B C : Type)
variable (f : A → B)
variable (g : C → B)

/-Oppgave 4.i -/
example (v : A → C) (c : f = g ∘ v) : f '' univ ⊆  g '' univ :=
begin
  rintros b ⟨a, ha⟩,
  use [v a, mem_univ (v a)],
  rw ← ha.2,
  rw c,
end

/-Oppgave 4.ii -/
/- Thanks to Alex Best on the Zulip chat for showing me how to finish this one. -/
example (s : f '' univ ⊆ g '' univ) : ∃ (v : A → C), f = g ∘ v :=
begin
  let v : A → C,
  { intro a,
    have h1 : f a ∈ g '' univ,
    { apply s,
      simp, },
    choose c hc using h1,
    exact c, },
  { use v,
    ext x,
    simp [v],
    generalize_proofs h,
    rw some_spec h, },
end
end oppgave_4