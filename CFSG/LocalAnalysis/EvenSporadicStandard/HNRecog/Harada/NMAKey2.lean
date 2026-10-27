module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.NMAKey
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.NMAOrder
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.ZStabTrans

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G}

private theorem qm_tv' : qm tv = 1 := by
  decide +kernel

private theorem add_self_eq_zero_V6 (v : V6) : v + v = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (v i)

private theorem zmod2_eq_one_of_ne_zero {c : ZMod 2} (h : c ≠ 0) : c = 1 := by
  have hval : c.val ≠ 0 := fun hv => h ((ZMod.val_eq_zero c).1 hv)
  have h1 : c.val = 1 := by have := ZMod.val_lt c; omega
  exact (ZMod.val_eq_one (by norm_num : 1 < 2) c).1 h1

private theorem zmod2_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  by_cases h : c = 0
  · exact Or.inl h
  · exact Or.inr (zmod2_eq_one_of_ne_zero h)

private theorem coordElt_injective {G : Type} [Group G] {ι : Elem2 6 →* G}
    (hι : Function.Injective ι) : Function.Injective (coordElt ι) := by
  intro u v huv
  have h : Multiplicative.ofAdd u = Multiplicative.ofAdd v := hι huv
  simpa using congrArg Multiplicative.toAdd h

private theorem mem_zpowers_two {z y : G} (hz : z ^ 2 = 1) (hzne : z ≠ 1)
    (hy : y ∈ zpowers z) : y = 1 ∨ y = z := by
  classical
  have hord : orderOf z = 2 := orderOf_eq_prime (p := 2) hz hzne
  rw [mem_zpowers_iff_mem_range_orderOf, hord, Finset.mem_image] at hy
  obtain ⟨n, hn, hny⟩ := hy
  rw [Finset.mem_range] at hn
  have hn' : n = 0 ∨ n = 1 := by omega
  rcases hn' with h | h
  · left; rw [← hny, h]; simp
  · right; rw [← hny, h]; simp

theorem Setting25.bil_tv_zv (h : Setting25 G t z z₁ ι zv R0 F) : bil tv zv = 0 := by
  rw [bil_comm, ← lam_eq_bil, h.hD2.lam_zv]

theorem Setting25.exists_lift_lam_zero (h : Setting25 G t z z₁ ι zv R0 F) {u u' : V6}
    (hu : bil u zv = 0) (hu' : bil u' zv = 0) :
    ∃ k ∈ Kgrp ι z, ∃ g ∈ OmegaMinus, Acts ι k g ∧ g zv = zv ∧ lam (g u) = 0 ∧
      lam (g u') = 0 := by
  obtain ⟨t', ht'q, ht'w, ht'u, ht'u'⟩ :=
    exists_nonsing_perp_pair h.hD2.qm_zv h.zv_ne_zero hu hu'
  obtain ⟨g, hgOm, hgzv, hgt'⟩ :=
    exists_omega_fix_nonsing h.hD2.qm_zv h.zv_ne_zero ht'q ht'w qm_tv' h.bil_tv_zv
  have hgu : lam (g u) = 0 := by
    rw [lam_eq_bil, ← hgt', bil_apply_of_mem_omegaMinus hgOm, bil_comm, ht'u]
  have hgu' : lam (g u') = 0 := by
    rw [lam_eq_bil, ← hgt', bil_apply_of_mem_omegaMinus hgOm, bil_comm, ht'u']
  obtain ⟨k, hk, hkActs⟩ := h.exists_mem_K_acts hgOm hgzv
  exact ⟨k, hk, g, hgOm, hkActs, hgzv, hgu, hgu'⟩

theorem Setting25.mem_R0_of_isRCand (h : Setting25 G t z z₁ ι zv R0 F) {x : G} {u : V6}
    (hx : IsRCand ι z zv x u) (hlam : lam u = 0) : x ∈ R0 := by
  obtain ⟨r, hr, hrAct⟩ := h.hD2.R0_surj u hx.1.1 hlam
  have hr_eich : EichActs ι zv r u := ⟨hx.1.1, hrAct⟩
  by_cases hu : u = 0 ∨ u = zv
  · have hxr : x ∈ ι.range :=
      EichActs.mem_range_of_eq_zero_or_eq (w := zv) h.centralizer_le h.hD2.qm_zv hx.1 hu
    obtain ⟨v, hv, hxv⟩ := mem_Cgrp.mp (hx.2.2 hxr)
    rw [← hxv]
    exact (h.hD2.R0_inter v).mpr hv
  · push Not at hu
    obtain ⟨hu0, huzv⟩ := hu
    have hrinv : r⁻¹ * x ∈ ι.range :=
      EichActs.inv_mul_mem_range (w := zv) h.centralizer_le h.hD2.qm_zv hr_eich hx.1
        (Or.inl (add_self_eq_zero_V6 u))
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hrinv
    set a : V6 := Multiplicative.toAdd b with ha
    have hca : coordElt ι a = r⁻¹ * x := by
      rw [ha]
      exact hb
    have hx_eq : x = r * coordElt ι a := by
      rw [hca]; group
    have hrsq : r ^ 2 ∈ zpowers z := h.hD2.R0_sq r hr
    have hsq_mem : coordElt ι (bil a zv • u + (bil a u + qm u * bil a zv) • zv) ∈
        zpowers z := by
      have h1 : (r ^ 2)⁻¹ * (x ^ 2) ∈ zpowers z := mul_mem (inv_mem hrsq) hx.2.1
      rw [hx_eq, hr_eich.sq_mul_coord a] at h1
      simpa only [inv_mul_cancel_left] using h1
    have hc_zpow : coordElt ι (bil a zv • u + (bil a u + qm u * bil a zv) • zv) = 1 ∨
        coordElt ι (bil a zv • u + (bil a u + qm u * bil a zv) • zv) = z :=
      mem_zpowers_two h.z_sq h.z_ne_one hsq_mem
    have hc0_or : bil a zv • u + (bil a u + qm u * bil a zv) • zv = 0 ∨
        bil a zv • u + (bil a u + qm u * bil a zv) • zv = zv := by
      rcases hc_zpow with hc | hc
      · left
        apply coordElt_injective h.injective_ι
        rw [hc, coordElt_zero]
      · right
        apply coordElt_injective h.injective_ι
        rw [hc, h.coord_z]
    have hba0 : bil a zv = 0 := by
      by_contra hba
      have hba1 : bil a zv = 1 := zmod2_eq_one_of_ne_zero hba
      have hc' : u + (bil a u + qm u * 1) • zv = 0 ∨
          u + (bil a u + qm u * 1) • zv = zv := by
        rw [hba1, one_smul] at hc0_or
        exact hc0_or
      rcases zmod2_eq_zero_or_one (bil a u + qm u * 1) with hd | hd
      · rcases hc' with hc | hc
        · exact hu0 (by rw [hd, zero_smul, add_zero] at hc; exact hc)
        · exact huzv (by rw [hd, zero_smul, add_zero] at hc; exact hc)
      · rcases hc' with hc | hc
        · apply huzv
          rw [hd, one_smul] at hc
          have h3 : u + zv = zv + zv := by rw [hc, add_self_eq_zero_V6]
          exact add_right_cancel h3
        · apply hu0
          rw [hd, one_smul] at hc
          have h3 : u + zv = 0 + zv := by rw [hc, zero_add]
          exact add_right_cancel h3
    have hcaR0 : coordElt ι a ∈ R0 := (h.hD2.R0_inter a).mpr hba0
    rw [hx_eq]
    exact mul_mem hr hcaR0

theorem Setting25.exists_isRCand_of_mem_R0 (h : Setting25 G t z z₁ ι zv R0 F) {x : G}
    (hx : x ∈ R0) : ∃ u : V6, IsRCand ι z zv x u ∧ lam u = 0 := by
  obtain ⟨u, hu, hlam, hact⟩ := h.hD2.R0_eichler x hx
  refine ⟨u, ⟨⟨hu, hact⟩, h.hD2.R0_sq x hx, ?_⟩, hlam⟩
  rintro ⟨b, hb⟩
  have hcoord : coordElt ι (Multiplicative.toAdd b) = x := hb
  exact mem_Cgrp.mpr ⟨Multiplicative.toAdd b,
    (h.hD2.R0_inter (Multiplicative.toAdd b)).mp (by rw [hcoord]; exact hx), hcoord⟩

theorem Setting25.exists_conj_mem_R0 (h : Setting25 G t z z₁ ι zv R0 F) {x y : G} {u u' : V6}
    (hx : IsRCand ι z zv x u) (hy : IsRCand ι z zv y u') :
    ∃ k ∈ Kgrp ι z, k * x * k⁻¹ ∈ R0 ∧ k * y * k⁻¹ ∈ R0 := by
  obtain ⟨k, hk, g, hgOm, hkActs, hgzv, hlamgu, hlamgu'⟩ :=
    h.exists_lift_lam_zero hx.1.1 hy.1.1
  have hz : k * z * k⁻¹ = z := by
    rw [← h.coord_z]
    exact Acts.apply_coord_of_fix hkActs hgzv
  refine ⟨k, hk, ?_, ?_⟩
  · exact h.mem_R0_of_isRCand
      (IsRCand.conj hkActs (omegaMinus_le_orthMinus hgOm) hgzv hz hx) hlamgu
  · exact h.mem_R0_of_isRCand
      (IsRCand.conj hkActs (omegaMinus_le_orthMinus hgOm) hgzv hz hy) hlamgu'

theorem Setting25.exists_isRCand (h : Setting25 G t z z₁ ι zv R0 F) {u : V6}
    (hu : bil u zv = 0) : ∃ x : G, IsRCand ι z zv x u := by
  obtain ⟨k, hk, g, hgOm, hkActs, hgzv, hlamgu, -⟩ := h.exists_lift_lam_zero hu hu
  have hbil : bil (g u) zv = 0 := by
    rw [← hgzv, bil_apply_of_mem_omegaMinus hgOm u zv, hu]
  obtain ⟨r, hr, hrAct⟩ := h.hD2.R0_surj (g u) hbil hlamgu
  have hr_eich : EichActs ι zv r (g u) := ⟨hbil, hrAct⟩
  have hrcand : IsRCand ι z zv r (g u) := by
    refine ⟨hr_eich, h.hD2.R0_sq r hr, ?_⟩
    rintro ⟨b, hb⟩
    have hcoord : coordElt ι (Multiplicative.toAdd b) = r := hb
    exact mem_Cgrp.mpr ⟨Multiplicative.toAdd b,
      (h.hD2.R0_inter (Multiplicative.toAdd b)).mp (by rw [hcoord]; exact hr), hcoord⟩
  have hgzv' : g⁻¹ zv = zv := by
    have h : g⁻¹ (g zv) = zv := by simp
    rwa [hgzv] at h
  have hz : k * z * k⁻¹ = z := by
    rw [← h.coord_z]
    exact Acts.apply_coord_of_fix hkActs hgzv
  have hkz : k⁻¹ * z * (k⁻¹)⁻¹ = z := by
    rw [← h.coord_z]
    exact Acts.apply_coord_of_fix hkActs.inv hgzv'
  refine ⟨k⁻¹ * r * k, ?_⟩
  have hcand := IsRCand.conj (k := k⁻¹) (g := g⁻¹) hkActs.inv
    (omegaMinus_le_orthMinus (inv_mem hgOm)) hgzv' hkz hrcand
  simpa [inv_inv] using hcand

end CFSG.EvenSporadicStandard.HNRecog.Harada
