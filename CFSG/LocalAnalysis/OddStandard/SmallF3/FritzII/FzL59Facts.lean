module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59Stmt

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup

variable {G : Type} [Group G]

structure Fz59T3Facts (t : G) (x₁ x₂ s : G) (T₃ : Subgroup G) : Prop where
  card_B : Nat.card (fz59B x₁ x₂ s) = 8
  card_F : Nat.card (fz59F t x₁ x₂ s) = 16
  B_nrm : ∀ g ∈ T₃, ∀ f ∈ fz59B x₁ x₂ s, g * f * g⁻¹ ∈ fz59B x₁ x₂ s
  F_nrm : ∀ g ∈ T₃, ∀ f ∈ fz59F t x₁ x₂ s, g * f * g⁻¹ ∈ fz59F t x₁ x₂ s
  F_elem : ∀ f ∈ fz59F t x₁ x₂ s, ∀ f' ∈ fz59F t x₁ x₂ s, f * f' = f' * f ∧ f ^ 2 = 1
  F_class : ∀ f ∈ fz59F t x₁ x₂ s, f ∉ fz59B x₁ x₂ s → ∃ g ∈ T₃, g * t * g⁻¹ = f
  cent_B : ∀ β ∈ fz59B x₁ x₂ s, β ≠ 1 → 2 ^ 8 ≤ Nat.card ↥(T₃ ⊓ centralizer ({β} : Set G))
  cent_t : Nat.card ↥(T₃ ⊓ centralizer ({t} : Set G)) = 2 ^ 7

end CFSG.OddStandard.SmallF3.FritzII
