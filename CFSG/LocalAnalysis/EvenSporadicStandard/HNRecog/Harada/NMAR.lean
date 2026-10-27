module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.NMAKey2

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G}

private lemma conj_mem_zpowers {z k w : G} (hk : k * z * k⁻¹ = z)
    (hw : w ∈ Subgroup.zpowers z) : k * w * k⁻¹ ∈ Subgroup.zpowers z := by
  rcases Subgroup.mem_zpowers_iff.mp hw with ⟨n, rfl⟩
  rw [← conj_zpow (a := k) (b := z) (i := n), hk]
  exact Subgroup.zpow_mem_zpowers z n

private lemma inv_conj_mem_zpowers {z k w : G} (hk : k * z * k⁻¹ = z)
    (hw : w ∈ Subgroup.zpowers z) : k⁻¹ * w * k ∈ Subgroup.zpowers z := by
  have hcomm : k * z = z * k := mul_inv_eq_iff_eq_mul.mp hk
  have hk' : k⁻¹ * z * (k⁻¹)⁻¹ = z := by
    rw [inv_inv]
    calc k⁻¹ * z * k = k⁻¹ * (z * k) := by group
      _ = k⁻¹ * (k * z) := by rw [hcomm.symm]
      _ = z := by group
  simpa using conj_mem_zpowers hk' hw

@[expose] def Rgrp (h : Setting25 G t z z₁ ι zv R0 F) : Subgroup G where
  carrier := {x | ∃ u : V6, IsRCand ι z zv x u}
  mul_mem' := by
    rintro x y ⟨u, hx⟩ ⟨u', hy⟩
    obtain ⟨k, hk, hkx, hky⟩ := h.exists_conj_mem_R0 hx hy
    have hcomm : k * z = z * k :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hk).2
    have hkz : k * z * k⁻¹ = z := mul_inv_eq_iff_eq_mul.mpr hcomm
    have hmem : (k * x * k⁻¹) * (k * y * k⁻¹) ∈ R0 := mul_mem hkx hky
    refine ⟨u + u', hx.1.mul hy.1, ?_, ?_⟩
    · have hsq : ((k * x * k⁻¹) * (k * y * k⁻¹)) ^ 2 ∈ Subgroup.zpowers z :=
        h.hD2.R0_sq _ hmem
      have heq : ((k * x * k⁻¹) * (k * y * k⁻¹)) ^ 2 = k * (x * y) ^ 2 * k⁻¹ := by
        rw [pow_two, pow_two]; group
      have htarget : (x * y) ^ 2 = k⁻¹ * ((k * x * k⁻¹) * (k * y * k⁻¹)) ^ 2 * k := by
        rw [heq]; group
      rw [htarget]
      exact inv_conj_mem_zpowers hkz hsq
    · intro hxy
      obtain ⟨g, hgOm, hgz, hkg⟩ := h.exists_acts_of_mem_K hk
      have hx'y'_range : (k * x * k⁻¹) * (k * y * k⁻¹) ∈ ι.range := by
        obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hxy
        have hv : coordElt ι (Multiplicative.toAdd a) = x * y := ha
        refine MonoidHom.mem_range.mpr
          ⟨Multiplicative.ofAdd (g (Multiplicative.toAdd a)), ?_⟩
        show coordElt ι (g (Multiplicative.toAdd a)) =
          (k * x * k⁻¹) * (k * y * k⁻¹)
        rw [← hkg (Multiplicative.toAdd a), hv]
        group
      have hC : (k * x * k⁻¹) * (k * y * k⁻¹) ∈ Cgrp ι zv := by
        obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hx'y'_range
        refine mem_Cgrp.mpr ⟨Multiplicative.toAdd a, ?_, ?_⟩
        · have hR0 : coordElt ι (Multiplicative.toAdd a) ∈ R0 := by
            show ι a ∈ R0
            rw [ha]
            exact hmem
          exact (h.hD2.R0_inter _).mp hR0
        · show ι a = (k * x * k⁻¹) * (k * y * k⁻¹)
          exact ha
      have hgzv : g⁻¹ zv = zv := by
        have h := Equiv.symm_apply_apply g zv
        rw [hgz] at h
        simpa using h
      have hconj : k⁻¹ * ((k * x * k⁻¹) * (k * y * k⁻¹)) * k ∈ Cgrp ι zv := by
        have h0 := Cgrp_conj hkg.inv (omegaMinus_le_orthMinus (inv_mem hgOm)) hgzv hC
        rwa [inv_inv] at h0
      rwa [show k⁻¹ * ((k * x * k⁻¹) * (k * y * k⁻¹)) * k = x * y from by group] at hconj
  one_mem' := ⟨0, IsRCand.one z zv⟩
  inv_mem' := by
    rintro x ⟨u, hx⟩
    exact ⟨u, hx.inv⟩

theorem Rgrp_le_K (h : Setting25 G t z z₁ ι zv R0 F) : Rgrp h ≤ Kgrp ι z := by
  rintro x ⟨u, hx⟩
  exact (h.mem_K_iff).mpr
    ⟨eichPerm zv u hx.1.1, hx.1.acts, by rw [eichPerm_apply, eichF_apply_w hx.1.1]⟩

theorem Rgrp_conj (h : Setting25 G t z z₁ ι zv R0 F) {k x : G} (hk : k ∈ Kgrp ι z)
    (hx : x ∈ Rgrp h) : k * x * k⁻¹ ∈ Rgrp h := by
  obtain ⟨u, hx⟩ := hx
  obtain ⟨g, hgOm, hgz, hkg⟩ := h.exists_acts_of_mem_K hk
  have hcomm : k * z = z * k :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hk).2
  have hkz : k * z * k⁻¹ = z := mul_inv_eq_iff_eq_mul.mpr hcomm
  exact ⟨g u, IsRCand.conj hkg (omegaMinus_le_orthMinus hgOm) hgz hkz hx⟩

theorem R0_le_Rgrp (h : Setting25 G t z z₁ ι zv R0 F) : R0 ≤ Rgrp h := by
  intro x hx
  obtain ⟨u, hu, -⟩ := h.exists_isRCand_of_mem_R0 hx
  exact ⟨u, hu⟩

theorem Cgrp_le_Rgrp (h : Setting25 G t z z₁ ι zv R0 F) : Cgrp ι zv ≤ Rgrp h := by
  intro c hc
  have hsq : c ^ 2 ∈ Subgroup.zpowers z := by
    rw [Cgrp_sq hc]
    exact Subgroup.one_mem _
  exact ⟨0, EichActs.of_mem_range (Cgrp_le_range hc), hsq, fun _ => hc⟩

theorem Rgrp_inf_range (h : Setting25 G t z z₁ ι zv R0 F) : Rgrp h ⊓ ι.range = Cgrp ι zv := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨⟨u, hx⟩, hxr⟩
    exact hx.2.2 hxr
  · exact le_inf (Cgrp_le_Rgrp h) Cgrp_le_range

theorem z_mem_Rgrp (h : Setting25 G t z z₁ ι zv R0 F) : z ∈ Rgrp h := by
  have hz : z ∈ Cgrp ι zv := by
    rw [← h.coord_z]
    exact (coordElt_mem_Cgrp h.injective_ι).mpr (bil_self zv)
  exact Cgrp_le_Rgrp h hz

theorem Rgrp_sq (h : Setting25 G t z z₁ ι zv R0 F) {x : G} (hx : x ∈ Rgrp h) :
    x ^ 2 ∈ zpowers z := by
  obtain ⟨u, hu⟩ := hx
  exact hu.2.1

theorem Rgrp_comm (h : Setting25 G t z z₁ ι zv R0 F) {x y : G} (hx : x ∈ Rgrp h)
    (hy : y ∈ Rgrp h) : x * y * x⁻¹ * y⁻¹ ∈ zpowers z := by
  obtain ⟨u, hx⟩ := hx
  obtain ⟨u', hy⟩ := hy
  obtain ⟨k, hk, hkx, hky⟩ := h.exists_conj_mem_R0 hx hy
  have hcomm : k * z = z * k :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hk).2
  have hkz : k * z * k⁻¹ = z := mul_inv_eq_iff_eq_mul.mpr hcomm
  have hc := h.hD2.R0_comm _ hkx _ hky
  have heq : k⁻¹ * ((k * x * k⁻¹) * (k * y * k⁻¹) * (k * x * k⁻¹)⁻¹ *
      (k * y * k⁻¹)⁻¹) * k = x * y * x⁻¹ * y⁻¹ := by group
  rw [← heq]
  exact inv_conj_mem_zpowers hkz hc

theorem Rgrp_eichActs (h : Setting25 G t z z₁ ι zv R0 F) {x : G} (hx : x ∈ Rgrp h) :
    ∃ u : V6, EichActs ι zv x u := by
  obtain ⟨u, hu⟩ := hx
  exact ⟨u, hu.1⟩

theorem exists_mem_Rgrp (h : Setting25 G t z z₁ ι zv R0 F) {u : V6} (hu : bil u zv = 0) :
    ∃ x ∈ Rgrp h, EichActs ι zv x u := by
  obtain ⟨x, hx⟩ := h.exists_isRCand hu
  exact ⟨x, ⟨u, hx⟩, hx.1⟩

end CFSG.EvenSporadicStandard.HNRecog.Harada
