module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.ConjugacySplit

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization

section Unipotent

variable {F : Type} [Field F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}

theorem unipotent_mem_zpowers_iff (t : F) :
    unipotentElement F b m hm heven t ∈ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) ↔
      t = 0 := by
  constructor
  · intro h
    have h0 := zpowers_cyclicGenerator_sq_smul F b m hm heven h (some 0)
    rw [unipotentElement_smul_some, zero_add, Option.some.injEq] at h0
    exact h0
  · rintro rfl
    rw [unipotentElement_zero]
    exact Subgroup.one_mem _

theorem zpowers_inf_unipotentSubgroup :
    Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) ⊓ unipotentSubgroup F b m hm heven =
      ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hgA, hgU⟩
  obtain ⟨t, rfl⟩ := (mem_unipotentSubgroup_iff F b m hm heven g).mp hgU
  rw [(unipotent_mem_zpowers_iff t).mp hgA, unipotentElement_zero]
  exact Subgroup.one_mem _

theorem alpha_unipotent_injective {α α' : CentralExtension F b m hm heven} {t t' : F}
    (hα : α ∈ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2))
    (hα' : α' ∈ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2))
    (h : α * unipotentElement F b m hm heven t = α' * unipotentElement F b m hm heven t') :
    α = α' ∧ t = t' := by
  have hmem : unipotentElement F b m hm heven (t + -t') ∈
      Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) := by
    rw [unipotentElement_add, ← unipotentElement_neg_eq]
    have : unipotentElement F b m hm heven t * (unipotentElement F b m hm heven t')⁻¹ =
        α⁻¹ * α' := by
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, h, mul_inv_cancel_right]
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hα) hα'
  have htt : t = t' := by
    have := (unipotent_mem_zpowers_iff _).mp hmem
    linear_combination this
  subst htt
  exact ⟨mul_right_cancel h, rfl⟩

theorem card_centralizer_unipotent [Fintype F] (hb : ¬ IsSquare b) :
    Nat.card (Subgroup.centralizer {unipotentElement F b m hm heven 1}) =
      m * Nat.card F := by
  have h2 := two_ne_zero_of_not_isSquare hb
  let e : Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) × F →
      Subgroup.centralizer {unipotentElement F b m hm heven 1} := fun p =>
    ⟨p.1 * unipotentElement F b m hm heven p.2,
      (mem_centralizer_unipotent_iff hb _).mpr ⟨p.1, p.1.2, p.2, rfl⟩⟩
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨α, t⟩ ⟨α', t'⟩ h
      obtain ⟨h1, h2'⟩ := alpha_unipotent_injective α.2 α'.2 (congrArg Subtype.val h)
      exact Prod.ext (Subtype.ext h1) h2'
    · rintro ⟨g, hg⟩
      obtain ⟨α, hα, t, rfl⟩ := (mem_centralizer_unipotent_iff hb g).mp hg
      exact ⟨(⟨α, hα⟩, t), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective e he), Nat.card_prod, Nat.card_zpowers,
    orderOf_cyclicGenerator_sq F b m hm heven h2]

theorem centralizer_alpha_unipotent {α : CentralExtension F b m hm heven}
    (hα : α ∈ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) :
    Subgroup.centralizer {α * unipotentElement F b m hm heven 1} =
      Subgroup.centralizer {unipotentElement F b m hm heven 1} := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    rw [← mul_assoc, ← cyclicGenerator_sq_zpowers_comm hα g] at h
    simp only [mul_assoc] at h
    exact mul_left_cancel h
  · intro h
    rw [← mul_assoc, ← cyclicGenerator_sq_zpowers_comm hα g, mul_assoc, h, mul_assoc]

theorem baseResidue_zpowers_eq_one {δ : CentralExtension F b m hm heven}
    (hδ : δ ∈ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2))
    (hres : baseResidue F b m hm heven δ = 1) :
    δ = 1 ∨ δ = cyclicGenerator F b m hm heven ^ m := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hδ
  have hu : baseResidue F b m hm heven (cyclicGenerator F b m hm heven) =
      Multiplicative.ofAdd 1 := by rw [cyclicGenerator, baseResidue_quotientClass, map_one]
  rw [map_zpow, map_pow, hu, ← ofAdd_nsmul, ← ofAdd_zsmul] at hres
  have h2n : ((2 * n : ℤ) : ZMod m) = 0 := by
    have := congrArg Multiplicative.toAdd hres
    simp only [toAdd_ofAdd, toAdd_one, nsmul_eq_mul, zsmul_eq_mul] at this
    push_cast
    linear_combination this
  obtain ⟨l, hl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mp h2n
  obtain ⟨k, hk⟩ := id heven
  have hn : n = k * l := by
    have : (2 : ℤ) * n = 2 * (k * l) := by rw [hl]; push_cast [hk]; ring
    linarith
  have hx : (cyclicGenerator F b m hm heven ^ 2) ^ n =
      (cyclicGenerator F b m hm heven ^ m) ^ l := by
    rw [hn, ← zpow_natCast, ← _root_.zpow_mul, ← zpow_natCast, ← _root_.zpow_mul]
    congr 1
    push_cast [hk]
    ring
  rw [hx]
  have hx2 : (cyclicGenerator F b m hm heven ^ m) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm m 2, cyclicGenerator_pow_two_m]
  rcases Int.even_or_odd l with ⟨j, hj⟩ | ⟨j, hj⟩
  · left
    rw [hj, ← two_mul, _root_.zpow_mul, zpow_ofNat, hx2, _root_.one_zpow]
  · right
    rw [hj, _root_.zpow_add, _root_.zpow_mul, zpow_ofNat, hx2, _root_.one_zpow, one_mul,
      zpow_one]

theorem alpha_eq_of_isConj {p : ℕ} (hpodd : Odd p) [CharP F p]
    (h2 : (2 : F) ≠ 0) {α α' : CentralExtension F b m hm heven}
    (hα : α ∈ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2))
    (hα' : α' ∈ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2))
    (h : IsConj (α * unipotentElement F b m hm heven 1) (α' * unipotentElement F b m hm heven 1)) :
    α = α' := by
  obtain ⟨k, hk⟩ := isConj_iff.mp h
  set δ := α⁻¹ * α' with hδ
  have hδA : δ ∈ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hα) hα'
  have hkU : k * unipotentElement F b m hm heven 1 * k⁻¹ =
      δ * unipotentElement F b m hm heven 1 := by
    have h1 : k * (α * unipotentElement F b m hm heven 1) * k⁻¹ =
        α * (k * unipotentElement F b m hm heven 1 * k⁻¹) := by
      rw [← mul_assoc k α, ← cyclicGenerator_sq_zpowers_comm hα k]
      group
    rw [h1] at hk
    rw [hδ, mul_assoc α⁻¹, ← hk]
    group
  have hres : baseResidue F b m hm heven δ = 1 := by
    have h1 := congrArg (baseResidue F b m hm heven) hkU
    rw [map_mul, map_mul, map_inv, mul_comm (baseResidue F b m hm heven k), mul_assoc,
      mul_inv_cancel, mul_one, map_mul] at h1
    have hU : baseResidue F b m hm heven (unipotentElement F b m hm heven 1) = 1 :=
      baseResidue_specialInclusion F b m hm heven _
    rw [hU, mul_one] at h1
    exact h1.symm
  have hδ1 : δ = 1 := by
    rcases baseResidue_zpowers_eq_one hδA hres with h1 | hx
    · exact h1
    · exfalso
      have hUp : unipotentElement F b m hm heven 1 ^ p = 1 := by
        rw [unipotentElement_pow, CharP.cast_eq_zero F p, zero_mul, unipotentElement_zero]
      have hlhs : (k * unipotentElement F b m hm heven 1 * k⁻¹) ^ p = 1 := by
        rw [conj_pow, hUp, mul_one, mul_inv_cancel]
      rw [hkU, hx] at hlhs
      have hcomm : Commute (cyclicGenerator F b m hm heven ^ m)
          (unipotentElement F b m hm heven 1) := cyclicGenerator_pow_m_comm F b m hm heven _
      rw [hcomm.mul_pow, hUp, mul_one] at hlhs
      obtain ⟨j, hj⟩ := hpodd
      have hx2 : (cyclicGenerator F b m hm heven ^ m) ^ 2 = 1 := by
        rw [← pow_mul, mul_comm m 2, cyclicGenerator_pow_two_m]
      rw [hj, pow_succ, pow_mul, hx2, one_pow, one_mul] at hlhs
      have hord := orderOf_cyclicGenerator F b m hm heven h2
      have : orderOf (cyclicGenerator F b m hm heven) ∣ m := orderOf_dvd_of_pow_eq_one hlhs
      rw [hord] at this
      have := Nat.le_of_dvd hm this
      omega
  rw [hδ, inv_mul_eq_one] at hδ1
  exact hδ1

theorem isConj_mul_central {α g g' : CentralExtension F b m hm heven}
    (hα : α ∈ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) (h : IsConj g g') :
    IsConj (α * g) (α * g') := by
  obtain ⟨k, rfl⟩ := isConj_iff.mp h
  refine isConj_iff.mpr ⟨k, ?_⟩
  rw [← mul_assoc, ← cyclicGenerator_sq_zpowers_comm hα k]
  group

theorem isConj_alpha_unipotent_iff [Finite F] {p : ℕ} (hpodd : Odd p) [CharP F p]
    (hb : ¬ IsSquare b) {α α' : CentralExtension F b m hm heven}
    (hα : α ∈ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2))
    (hα' : α' ∈ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) (t : F) :
    IsConj (α * unipotentElement F b m hm heven 1) (α' * unipotentElement F b m hm heven t) ↔
      α' = α ∧ t ≠ 0 := by
  have h2 := two_ne_zero_of_not_isSquare hb
  constructor
  · intro h
    have ht : t ≠ 0 := by
      rintro rfl
      rw [unipotentElement_zero, mul_one] at h
      obtain ⟨k, hk⟩ := isConj_iff.mp h.symm
      rw [← cyclicGenerator_sq_zpowers_comm hα' k, mul_inv_cancel_right] at hk
      have hU : unipotentElement F b m hm heven 1 ∈
          Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) := by
        rw [show unipotentElement F b m hm heven 1 = α⁻¹ * α' by
          rw [hk, inv_mul_cancel_left]]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hα) hα'
      exact one_ne_zero ((unipotent_mem_zpowers_iff 1).mp hU)
    refine ⟨?_, ht⟩
    have h' : IsConj (α' * unipotentElement F b m hm heven t)
        (α' * unipotentElement F b m hm heven 1) :=
      isConj_mul_central hα' (isConj_unipotent (hm := hm) (heven := heven) hb ht).symm
    exact (alpha_eq_of_isConj hpodd h2 hα hα' (h.trans h')).symm
  · rintro ⟨rfl, ht⟩
    exact isConj_mul_central hα (isConj_unipotent (hm := hm) (heven := heven) hb ht)

end Unipotent

end CFSG.Wreathed.CentralSL2
