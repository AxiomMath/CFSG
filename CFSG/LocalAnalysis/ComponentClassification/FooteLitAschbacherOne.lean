module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCases

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup
open scoped MatrixGroups

@[expose] def IsCoverOverTwo (Y : Type*) [Group Y] (X : Type*) [Group X] : Prop :=
  ∃ π : Y →* X, Function.Surjective π ∧ π.ker ≤ center Y ∧ π.ker ≤ commutator Y ∧
    Nat.card π.ker = 2

@[expose] def IsCentralSquareSL25 {X : Type*} [Group X] (L : Subgroup X) : Prop :=
  ∃ L₁ L₂ : Subgroup X, L₁ ⊔ L₂ = L ∧ (∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) ∧
    Nat.card ↥(L₁ ⊓ L₂) = 2 ∧ Nonempty (L₁ ≃* SL(2, ZMod 5)) ∧ Nonempty (L₂ ≃* SL(2, ZMod 5))

end CFSG.ComponentClassification.FooteLit
