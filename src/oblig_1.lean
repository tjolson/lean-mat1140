 -- **MAT1140 Strukturer og argumenter - Høst 2021 Oblig 1, formalized in Lean** --

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
  sorry
end

/-Oppgave 1.ii-/
/-Again this exercise is already in the mathlib as `union_eq_left_iff_subset`.-/
example (A B : set U) : A ∪ B = A ↔ B ⊆ A :=
begin
  sorry
end

/-Oppgave 2.i-/
/-In 1, A and B were arbitrary sets, here they were meant to be arbitrary subsets of some set U. We
could have simulated this by declaring a new type α and letting A, B and U be of type `set α` and
introducing hypotheses of type `A ⊆ U` and `B ⊆ U`, but the logic behind a solution would be the same 
and we can still access U as a "set" with `univ`. One downside is that we can no longer define the map 
Φ in the problem with codomain 𝒫(A) × 𝒫(B), since functions (avbildninger) in Lean always go between
types and we still want to think of the elements of 𝒫(A) as subsets of A (which are subsets of U). By
spelling out for Lean what sujectivity and injectivity mean for *this problem* we still reason the way 
we would naturally. -/
example : (∀ (C D : set U), C ⊆ A ∧ D ⊆ B → ∃ (V : set U), (C, D) =  (V ∩ A, V ∩ B)) → (A ∩ B = ∅) :=
begin
  sorry
end

/-Oppgave 2.ii-/
/-It may be useful to recall that `simp` will change goals or hypotheses (X,Y) = (X',Y') and return 
what this means for the components: X = X' ∧ Y = Y'.-/
example : (A ∩ B = ∅) → (∀ (C D : set U), C ⊆ A ∧ D ⊆ B → ∃ (V : set U), (C, D) =  (V ∩ A, V ∩ B)) :=
begin
  sorry
end

/-Oppgave 2.iii -/
example : (∀ (V W : set U), (V ∩ A, V ∩ B) = (W ∩ A, W ∩ B) → V = W) → (univ = A ∪ B) :=
begin
  sorry
end

/-Oppgave 2.iv -/
example : (univ = A ∪ B) → (∀ (V W : set U), (V ∩ A, V ∩ B) = (W ∩ A, W ∩ B) → V = W) :=
begin
  sorry
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
  sorry
end

/-Oppgave 3.ii -/
/-Here we see a less trivial difference in doing mathematics on paper and in a computer. Lean would
seem to prefer functions being defined explicitly. It does manage, though I'm not quite yet sure how
it works. Note also that in this problem and 4.ii we have to invoke choice. -/
local attribute [instance] prop_decidable
-- Including `(c : C)` to instist that C is not empty, as in the problem. 
example (c : C) (t : ∀ (x x' : A), f x = f x' → g x = g x') : ∃ u : B → C, g = u ∘ f :=
begin
  sorry
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
  sorry
end

/-Oppgave 4.ii -/
example (s : f '' univ ⊆ g '' univ) : ∃ (v : A → C), f = g ∘ v :=
begin
  sorry
end
end oppgave_4