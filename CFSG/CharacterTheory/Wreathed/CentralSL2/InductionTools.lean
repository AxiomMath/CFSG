module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.InducedStabilizer

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open TwoRankLowerBound.Helpers

section Tools

variable {K : Type} [Group K] [Fintype K]

theorem inducedFunction_stages {B I : Subgroup K} (hBI : B ≤ I) (f : B → ℂ) :
    inducedFunction I (inducedFunction (B.subgroupOf I) fun b => f ⟨((b : I) : K), b.2⟩) =
      inducedFunction B f := by
  funext g
  have hcard : Nat.card (B.subgroupOf I) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBI).toEquiv
  have hE : ∀ k : K, extendByZero I (inducedFunction (B.subgroupOf I)
      fun b => f ⟨((b : I) : K), b.2⟩) k =
        (Nat.card B : ℂ)⁻¹ * ∑ y : I, extendByZero B f ((y : K)⁻¹ * k * y) := by
    intro k
    by_cases hk : k ∈ I
    · rw [extendByZero_of_mem I _ hk, inducedFunction_eq_extendByZero, hcard]
      rfl
    · rw [extendByZero_of_not_mem I _ hk]
      symm
      rw [Finset.sum_eq_zero, mul_zero]
      intro y _
      apply extendByZero_of_not_mem
      intro hm
      apply hk
      have h1 := I.mul_mem (I.mul_mem y.2 (hBI hm)) (I.inv_mem y.2)
      have h2 : (y : K) * ((y : K)⁻¹ * k * y) * (y : K)⁻¹ = k := by group
      rwa [h2] at h1
  rw [inducedFunction_eq_extendByZero, inducedFunction_eq_extendByZero]
  simp_rw [hE]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hreindex : ∀ y : I, ∑ x : K, extendByZero B f ((y : K)⁻¹ * (x⁻¹ * g * x) * y) =
      ∑ x : K, extendByZero B f (x⁻¹ * g * x) := by
    intro y
    refine Fintype.sum_equiv (Equiv.mulRight (y : K)) _ _ fun x => ?_
    congr 1
    simp only [Equiv.coe_mulRight]
    group
  rw [Finset.sum_congr rfl fun y _ => hreindex y, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card]
  have hI : (Nat.card I : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp

theorem inducedFunction_mul_classFunction (H : Subgroup K) (f : H → ℂ) {χ : K → ℂ}
    (hχ : BlocksIsClassFunction χ) (g : K) :
    inducedFunction H (fun h => f h * χ h) g = inducedFunction H f g * χ g := by
  rw [inducedFunction_eq_extendByZero, inducedFunction_eq_extendByZero, mul_assoc,
    Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x⁻¹ * g * x ∈ H
  · rw [extendByZero_of_mem _ _ hx, extendByZero_of_mem _ _ hx]
    congr 1
    have h1 := hχ g x⁻¹
    rw [inv_inv] at h1
    exact h1
  · rw [extendByZero_of_not_mem _ _ hx, extendByZero_of_not_mem _ _ hx, zero_mul]

theorem inducedFunction_mulEquiv (α : K ≃* K) (H : Subgroup K) (hH : ∀ x, α x ∈ H ↔ x ∈ H)
    (f : H → ℂ) (g : K) :
    inducedFunction H f (α g) = inducedFunction H (fun h => f ⟨α h, (hH h).mpr h.2⟩) g := by
  rw [inducedFunction_eq_extendByZero, inducedFunction_eq_extendByZero]
  congr 1
  symm
  refine Fintype.sum_equiv α.toEquiv _ _ fun y => ?_
  have hα : (α.toEquiv y)⁻¹ * α g * α.toEquiv y = α (y⁻¹ * g * y) := by
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, map_mul, map_inv]
  rw [hα]
  by_cases hy : y⁻¹ * g * y ∈ H
  · rw [extendByZero_of_mem _ _ hy, extendByZero_of_mem _ _ ((hH _).mpr hy)]
  · rw [extendByZero_of_not_mem _ _ hy,
      extendByZero_of_not_mem _ _ (fun h => hy ((hH _).mp h))]

end Tools

end CFSG.Wreathed.CentralSL2
