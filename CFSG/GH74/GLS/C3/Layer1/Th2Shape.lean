module

public import CFSG.GH74.GLS.C3.Layer1.Th2Defs

public section

namespace CFSG.GH74.GLS.Th2

open Subgroup CFSG.ABGLocalTools

@[expose] def RankTwoShape {G : Type} [Group G] (P : Subgroup G) : Prop :=
  (∀ A : Subgroup G, A ≤ P → CFSG.IsElementaryAbelian 2 ↥A → Nat.card ↥A ≤ 4) ∧
  (∀ A : Subgroup G, A ≤ P → CFSG.IsElementaryAbelian 2 ↥A → ∃ U : Subgroup G, A ≤ U ∧ IsFourSub P U) ∧
  (∀ U₁ U₂ : Subgroup G, IsFourSub P U₁ → IsFourSub P U₂ → ∃ z ∈ U₁, z ∈ U₂ ∧ orderOf z = 2)

end CFSG.GH74.GLS.Th2
