module

public import Mathlib.Tactic.Group
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Algebra.Group.Subgroup.Finite

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

variable {G : Type} [Group G]

theorem y6_card_le_two_mul [Finite G] {C Y : Subgroup G} (hYC : Y ≤ C)
    (h3 : ∀ x ∈ C, ∀ y ∈ C, x ∈ Y ∨ y ∈ Y ∨ x⁻¹ * y ∈ Y) : Nat.card ↥C ≤ 2 * Nat.card ↥Y := by
  classical
  by_cases hCY : C ≤ Y
  · have hEq : C = Y := le_antisymm hCY hYC
    subst hEq
    omega
  · obtain ⟨x₀, hx₀C, hx₀Y⟩ := Set.not_subset.1 hCY
    let f : ↥Y ⊕ ↥Y → ↥C := fun s =>
      match s with
      | Sum.inl y => ⟨y, hYC y.2⟩
      | Sum.inr y => ⟨x₀ * y, C.mul_mem hx₀C (hYC y.2)⟩
    have hsurj : Function.Surjective f := by
      rintro ⟨c, hcC⟩
      by_cases hcY : c ∈ Y
      · refine ⟨Sum.inl ⟨c, hcY⟩, ?_⟩
        apply Subtype.ext
        rfl
      · have hmem : x₀⁻¹ * c ∈ Y := by
          rcases h3 x₀ hx₀C c hcC with h | h | h
          · exact absurd h hx₀Y
          · exact absurd h hcY
          · exact h
        refine ⟨Sum.inr ⟨x₀⁻¹ * c, hmem⟩, ?_⟩
        apply Subtype.ext
        change x₀ * (x₀⁻¹ * c) = c
        group
    have hle := Nat.card_le_card_of_surjective f hsurj
    rw [Nat.card_sum] at hle
    omega

end CFSG.OddStandard.HigherRank.YamadaG23
