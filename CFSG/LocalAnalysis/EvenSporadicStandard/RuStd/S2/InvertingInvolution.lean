module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.Interfaces

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup

private theorem a5_inv : ∀ x : A5, x ^ 3 = 1 → x ≠ 1 →
    ∃ y : A5, y * y = 1 ∧ y ≠ 1 ∧ y * x * y = x⁻¹ := by
  set_option maxRecDepth 100000 in decide

theorem exists_inv_involution {Y : Type} [Group Y] (h5 : RuFiveFacts Y) (f r : Y)
    (hf : orderOf f = 5) (hr : orderOf r = 3) (hfr : f * r = r * f)
    (hA : Nat.card (centralizer ({f} : Set Y)) = 300) :
    ∃ d ∈ centralizer ({f} : Set Y), d * d = 1 ∧ d ≠ 1 ∧ d * r * d = r⁻¹ := by
  obtain ⟨D, ⟨eD⟩, hDle, hjoin, hdisj⟩ := h5.typeA f hf hA
  have hrC : r ∈ centralizer ({f} : Set Y) := by
    rw [mem_centralizer_singleton_iff]; exact hfr.symm
  have hDn : D ≤ normalizer (zpowers f : Set Y) := by
    rw [le_normalizer_iff]
    intro δ hδ k hk
    have hc := hDle hδ
    rw [mem_centralizer_singleton_iff] at hc
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hk
    have : δ * f ^ n * δ⁻¹ = f ^ n := by
      rw [(Commute.zpow_right (show Commute δ f from hc) n).eq]; group
    rw [this]; exact zpow_mem_zpowers f n
  have hrJ : (r : Y) ∈ ((zpowers f ⊔ D : Subgroup Y) : Set Y) := by
    rw [← hjoin]; exact hrC
  rw [coe_mul_of_right_le_normalizer_left _ _ hDn] at hrJ
  obtain ⟨a, ha, δ, hδ, hrad⟩ := hrJ
  have hδc : a * δ = δ * a := by
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp ha
    have hc := hDle hδ
    rw [mem_centralizer_singleton_iff] at hc
    exact (Commute.zpow_left (show Commute f δ from hc.symm) n).eq
  have ha1 : a = 1 := by
    have h3 : r ^ 3 = 1 := hr ▸ pow_orderOf_eq_one r
    rw [← hrad, (Commute.mul_pow hδc 3)] at h3
    have ha3 : a ^ 3 ∈ D := by
      have : a ^ 3 = (δ ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h3
      rw [this]; exact D.inv_mem (D.pow_mem hδ 3)
    have ha3' : a ^ 3 = 1 := hdisj.le_bot ⟨(zpowers f).pow_mem ha 3, ha3⟩
    have h1 : orderOf a ∣ 5 := hf ▸ orderOf_dvd_of_mem_zpowers ha
    have h2 : orderOf a ∣ 3 := orderOf_dvd_of_pow_eq_one ha3'
    have : orderOf a ∣ Nat.gcd 5 3 := Nat.dvd_gcd h1 h2
    norm_num at this
    exact this
  have hrD : r ∈ D := by
    have : r = δ := by rw [← hrad, ha1]; exact one_mul δ
    rw [this]; exact hδ
  set x : A5 := eD ⟨r, hrD⟩ with hx
  have hx3 : x ^ 3 = 1 := by
    rw [hx, ← map_pow]
    have : (⟨r, hrD⟩ : D) ^ 3 = 1 := Subtype.ext (by
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hr ▸ pow_orderOf_eq_one r)
    rw [this, map_one]
  have hx1 : x ≠ 1 := by
    intro h
    rw [hx, MulEquiv.map_eq_one_iff] at h
    have : r = 1 := congrArg Subtype.val h
    rw [this, orderOf_one] at hr; norm_num at hr
  obtain ⟨y, hy2, hy1, hyx⟩ := a5_inv x hx3 hx1
  refine ⟨(eD.symm y : Y), hDle (eD.symm y).2, ?_, ?_, ?_⟩
  · rw [← Subgroup.coe_mul, ← map_mul, hy2, map_one, Subgroup.coe_one]
  · intro h
    apply hy1
    have : eD.symm y = 1 := Subtype.ext h
    rwa [MulEquiv.map_eq_one_iff] at this
  · have : eD.symm y * ⟨r, hrD⟩ * eD.symm y = (⟨r, hrD⟩ : D)⁻¹ := by
      apply eD.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, map_inv, ← hx, hyx]
    exact congrArg Subtype.val this

end CFSG.EvenSporadicStandard.RuStd.S2
