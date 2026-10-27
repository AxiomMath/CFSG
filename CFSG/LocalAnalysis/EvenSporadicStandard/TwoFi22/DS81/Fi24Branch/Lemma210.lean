module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Facts

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

@[expose] def DS81Lemma210Strong : Prop :=
  ∀ (B : Type) [Group B] [Finite B] (Y : Subgroup B) [IsSimpleGroup ↥Y],
    (∃ a b : ↥Y, a * b ≠ b * a) → CFSG.Blueprint.Catalog ↥Y →
    (∃ (Yh : Type) (_ : Group Yh) (π : Yh →* ↥Y), Function.Surjective π ∧
      commutator Yh = ⊤ ∧ π.ker ≤ center Yh ∧ Nat.card π.ker = 2) →
    2 ^ 19 ∣ Nat.card ↥Y → ¬ 2 ^ 21 ∣ Nat.card ↥Y →
    ∀ y ∈ Y, orderOf y = 2 → ∀ A : Subgroup B, A = TwoFi22.O2In (Y ⊓ centralizer ({y} : Set B)) →
      Nat.card ↥A = 2 ^ 12 → (∀ a ∈ A, a ^ 2 = 1) →
      Y ⊓ centralizer ({y} : Set B) ⊓ centralizer (A : Set B) ≤ A →
      (∃ (X : Type) (_ : Group X) (π : ↥(Y ⊓ centralizer ({y} : Set B)) →* X),
        Function.Surjective π ∧ π.ker = A.subgroupOf (Y ⊓ centralizer ({y} : Set B)) ∧
        (IsU42Two X ∨ CFSG.Open.StatedClassicalModel X .PSU 4 2 1)) →
      False

@[expose] def CatalogOuterSolvable : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    CFSG.Blueprint.Catalog X →
    Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer X)

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
