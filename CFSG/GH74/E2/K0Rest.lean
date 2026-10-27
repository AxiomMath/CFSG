module

public import CFSG.GH74.E2.K0Simple

public section

namespace CFSG.GH74.E2

open Subgroup Blueprint

structure K0DataRest : Prop where
  autRank_ge5 : ∀ (K : Type) [Group K] [Finite K], K0Shape K → ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∀ B : Subgroup (MulAut K), ElemAb p B → Nat.card B ≤ p

structure K0Data3Rest : Prop where
  autRank3_le_two : ∀ (K : Type) [Group K] [Finite K], K0Shape K →
    ∀ R : Subgroup (MulAut K), ElemAb 3 R → Nat.card R ≤ 9
  autRank3_le_one : ∀ (K : Type) [Group K] [Finite K],
    (ShapeA5 K ∨ ShapeL27 K ∨ ShapeL217 K ∨ ShapeSz8 K ∨ Shape2Sz8 K) →
    ∀ R : Subgroup (MulAut K), ElemAb 3 R → Nat.card R ≤ 3
  rank_ge4_sz : ∀ (K : Type) [Group K] [Finite K], Shape2Sz8 K →
    ∃ U : Subgroup K, IsPGroup 2 U ∧ 4 ≤ Group.rank U
  inner3 : ∀ (K : Type) [Group K] [Finite K], (ShapeA6 K ∨ ShapeL33 K ∨ ShapeM11 K) →
    ∀ φ : MulAut K, φ ^ 3 = 1 → ∃ k : K, ∀ x : K, φ x = k * x * k⁻¹
  centralizer3 : ∀ (K : Type) [Group K] [Finite K], (ShapeA6 K ∨ ShapeL33 K ∨ ShapeM11 K) →
    ∀ B : Subgroup K, ElemAb 3 B → Nat.card B = 9 → ∀ k : K, (∀ b ∈ B, k * b = b * k) → k ∈ B
  inner3_small : ∀ (K : Type) [Group K] [Finite K], (ShapeA5 K ∨ ShapeL27 K ∨ ShapeL217 K) →
    ∀ φ : MulAut K, φ ^ 3 = 1 → ∃ k : K, ∀ x : K, φ x = k * x * k⁻¹
  autCentralizer : ∀ (K : Type) [Group K] [Finite K],
    (ShapeA6 K ∨ ShapeL28 K ∨ ShapeL33 K ∨ ShapeU33 K ∨ ShapeM11 K ∨ Shape2M12 K) →
    ∀ R : Subgroup (MulAut K), ElemAb 3 R → Nat.card R = 9 → ∀ ψ : MulAut K, ψ ^ 2 = 1 →
      (∀ r ∈ R, ψ * r = r * ψ) → ψ = 1

theorem k0Data_of_rest
    (h : K0DataRest) : K0Data where
  autRank_ge5 := h.autRank_ge5
  center_card := by
    intro K _ _ hK
    exact card_center_le_two_of_K0Shape hK
  sylow_rank_simple := by
    intro K _ _ hK hc
    exact exists_twoSubgroup_rank_two_of_K0Shape hK hc
  sylow_rank_cover := by
    intro K _ _ hK hc
    rcases shape2_of_K0Shape_center_ne_bot hK hc with hK2 | hK2
    · obtain ⟨U, hU, hr⟩ := rank_ge4_of_shape2M12 hK2
      exact ⟨U, hU, by omega⟩
    · exact rank_ge3_of_shape2Sz8 hK2

theorem k0Data3_of_rest
    (h : K0Data3Rest) : K0Data3 where
  autRank3_le_two := h.autRank3_le_two
  autRank3_le_one := h.autRank3_le_one
  rank_ge3 := by
    intro K _ _ hK
    rcases hK with hK | hK | hK
    · exact rank_ge3_of_shapeL28 hK
    · exact rank_ge3_of_shapeU33 hK
    · obtain ⟨U, hU, hr⟩ := rank_ge4_of_shape2M12 hK
      exact ⟨U, hU, by omega⟩
  rank_ge4 := by
    intro K _ _ hK
    exact rank_ge4_of_shape2M12 hK
  rank_ge3_sz := by
    intro K _ _ hK
    rcases hK with hK | hK
    · exact rank_ge3_of_shapeSz8 hK
    · exact rank_ge3_of_shape2Sz8 hK
  rank_ge4_sz := h.rank_ge4_sz
  inner3 := h.inner3
  centralizer3 := h.centralizer3
  center_bot := by
    intro K _ _ hK
    exact center_eq_bot_of_simpleShapes hK
  inner3_small := h.inner3_small
  autCentralizer := h.autCentralizer

end CFSG.GH74.E2
