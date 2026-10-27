module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1Facts

public section

namespace CFSG.ComponentClassification.HarrisLit.P1

open CFSG Subgroup DihedralGroup

theorem dihedral_involution : ∀ g : DihedralGroup 8, g * g = 1 → g ≠ 1 →
    g = r 4 ∨ ∃ i, g = sr i := by
  decide

theorem pow_four_of_pow_eight : ∀ σ : Equiv.Perm (Fin 6), σ ^ 8 = 1 → σ ^ 4 = 1 := by
  decide +kernel

theorem exists_reflection_mul {G : Type*} [Group G] [Finite G] {D L : Subgroup G}
    (e : ↥D ≃* DihedralGroup 8) (hL8 : ∀ g ∈ L, g ^ 8 = 1 → g ^ 4 = 1)
    (hDL : Nat.card ↥(D ⊓ L) = 8) {x : G} (hxD : x ∈ D) (hxL : x ∉ L) (hx2 : orderOf x = 2) :
    ∃ ℓ ∈ D ⊓ L, orderOf ℓ = 2 ∧ (x * ℓ) ^ 8 = 1 ∧ (x * ℓ) ^ 4 ∈ L ∧ (x * ℓ) ^ 4 ≠ 1 := by
  set H := L.subgroupOf D with hH
  have hcH : Nat.card ↥H = 8 := by
    rw [← hDL, inf_comm, ← subgroupOf_map_subtype, card_map_of_injective D.subtype_injective]
  have hcD : Nat.card ↥D = 16 := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hidx : H.index = 2 := by
    have h := card_mul_index H
    rw [hcH, hcD] at h
    omega
  set ρ : ↥D := e.symm (r 1) with hρ
  have hρ8 : orderOf ρ = 8 := by
    rw [hρ, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
  have hρ4 : ρ ^ 4 ∈ H := by
    rw [show ρ ^ 4 = (ρ ^ 2) ^ 2 by rw [← pow_mul]]
    exact sq_mem_of_index_two hidx _
  have hρH : ρ ∉ H := by
    intro h
    have h1 : ((ρ : G)) ^ 4 = 1 := hL8 _ h (by rw [← Subgroup.coe_pow, ← hρ8,
      pow_orderOf_eq_one, Subgroup.coe_one])
    have h2 : ρ ^ 4 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, h1, Subgroup.coe_one])
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hρ8] at h3
    norm_num at h3
  set x' : ↥D := ⟨x, hxD⟩ with hx'
  have hx'H : x' ∉ H := hxL
  have hx'2 : x' * x' = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one, ← pow_two, ← hx2]
    exact pow_orderOf_eq_one x
  set ℓ' := x' * ρ with hℓ'
  have hℓH : ℓ' ∈ H := (mul_mem_iff_of_index_two hidx).mpr (iff_of_false hx'H hρH)
  have hxℓ : x' * ℓ' = ρ := by
    rw [hℓ', ← mul_assoc, hx'2, one_mul]
  have hℓ2 : orderOf ℓ' = 2 := by
    have hex : e x' * e x' = 1 := by rw [← map_mul, hx'2, map_one]
    have hex1 : e x' ≠ 1 := by
      intro h
      apply hx'H
      rw [show x' = 1 from e.injective (by rw [h, map_one])]
      exact one_mem _
    rcases dihedral_involution (e x') hex hex1 with h4 | ⟨i, hi⟩
    · exfalso
      apply hx'H
      have h1 : x' = ρ ^ 4 := by
        apply e.injective
        rw [h4, hρ, map_pow, MulEquiv.apply_symm_apply, DihedralGroup.r_one_pow]
        rfl
      rw [h1]
      exact hρ4
    · rw [← MulEquiv.orderOf_eq e, hℓ', map_mul, hρ, MulEquiv.apply_symm_apply, hi,
        DihedralGroup.sr_mul_r, DihedralGroup.orderOf_sr]
  refine ⟨ℓ', ⟨ℓ'.2, hℓH⟩, by rw [Subgroup.orderOf_coe, hℓ2], ?_, ?_, ?_⟩
  · have h : x * (ℓ' : G) = (ρ : G) := by
      rw [← hxℓ, Subgroup.coe_mul]
      rfl
    rw [h, ← Subgroup.coe_pow, ← hρ8, pow_orderOf_eq_one, Subgroup.coe_one]
  · have h : (x * (ℓ' : G)) ^ 4 = ((ρ ^ 4 : ↥D) : G) := by
      rw [← hxℓ, Subgroup.coe_pow, Subgroup.coe_mul]
      rfl
    rw [h]
    exact hρ4
  · have h : (x * (ℓ' : G)) ^ 4 = ((ρ ^ 4 : ↥D) : G) := by
      rw [← hxℓ, Subgroup.coe_pow, Subgroup.coe_mul]
      rfl
    rw [h]
    intro h1
    have h2 : ρ ^ 4 = 1 := Subtype.ext (by rw [h1, Subgroup.coe_one])
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hρ8] at h3
    norm_num at h3

end CFSG.ComponentClassification.HarrisLit.P1
