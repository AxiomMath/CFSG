module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81F7

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable (d : Data H₁)

theorem eq_one_or_a_of_comm {π y : H} (hπ : π ∈ h.P) (hπb : π * d.b = d.b * π)
    (hy : y ∈ zpowers d.p) (hy1 : y ≠ 1) (hya : y ≠ h.a) (hπy : π * y = y * π) :
    π = 1 ∨ π = h.a := by
  obtain ⟨β, hP⟩ := d.pres
  obtain ⟨i, rfl | rfl⟩ := hP.mem_cases hπ
  · rw [← d.p_a]
    exact (hP.comm_b_iff (zpow_mem (mem_zpowers _) i)).mp hπb.symm
  · exfalso
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    have h1 : d.b * d.p ^ k = d.p ^ k * d.b := by
      have h2 : d.p ^ i * (d.b * d.p ^ k) = d.p ^ i * (d.p ^ k * d.b) := by
        calc d.p ^ i * (d.b * d.p ^ k) = d.p ^ i * d.b * d.p ^ k := by group
          _ = d.p ^ k * (d.p ^ i * d.b) := hπy
          _ = d.p ^ i * (d.p ^ k * d.b) := by
              rw [← mul_assoc, ← mul_assoc, ← zpow_add, ← zpow_add, add_comm]
      exact mul_left_cancel h2
    rcases (hP.comm_b_iff (zpow_mem (mem_zpowers _) k)).mp h1 with h3 | h3
    · exact hy1 h3
    · exact hya (h3.trans d.p_a)

theorem center_F_le (hRk : CFL2Rank) (hJ : CFL2J) (hC : CFL2C) (hSy : CFL2Sylow)
    (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement) (hCF23 : CFProp23Fusion)
    (hCF24 : CFProp24c) (hCFc : CFProp23Center) (hCF1 : CFSec8Simple)
    (hCF2 : CFSec8InnerCentralizer) (F : d.Facts) {w : H} (hwF : w ∈ h.F32)
    (hwc : ∀ v ∈ h.F32, w * v = v * w) :
    w ∈ zpowers d.z ⊔ zpowers h.a ⊔ zpowers d.sigma := by
  have hwS : w ∈ h.S := h.F32_le_S hwF
  have hzS : d.z ∈ h.S := h.toHyp52.D_le_S d.z_D
  have hDF := d.D_le_F hSy hCF1 hCF2 F
  have hρw : rhoS hwS ∈ Seven.rhoImg h.J h.S ⊓ centralizer ((Seven.rhoImg h.J h.D :
      Subgroup _) : Set (MulAut (h.J ⧸ pPrimeCore 2 h.J))) := by
    refine mem_inf.mpr ⟨rhoS_mem hwS hwS, ?_⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨⟨e, heN⟩, he, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hwc e (hDF (mem_subgroupOf.mp he))).symm
  have h1 := d.rhoS_inf_centralizer_le hC hCF1 hCF2 F hρw
  have hle : zpowers (rhoS hzS) ⊔ zpowers (rhoS d.tau_mem_S) ≤
      Seven.rhoImg h.J (zpowers d.z ⊔ zpowers d.tau) :=
    sup_le (zpowers_le.mpr (rhoS_mem hzS (mem_sup_left (mem_zpowers _))))
      (zpowers_le.mpr (rhoS_mem d.tau_mem_S (mem_sup_right (mem_zpowers _))))
  obtain ⟨c, hc, hcw⟩ := mem_map.mp (hle h1)
  have hcY : (c : H) ∈ zpowers d.z ⊔ zpowers d.tau := mem_subgroupOf.mp hc
  have hcS : (c : H) ∈ h.S := (sup_le (zpowers_le.mpr hzS) (zpowers_le.mpr d.tau_mem_S)) hcY
  have hπ : (c : H)⁻¹ * w ∈ h.P := by
    refine (rho_eq_one_iff (h := h) (mul_mem (inv_mem hcS) hwS)).mp ?_
    show Eight.oddBarAction h.J (c⁻¹ * ⟨w, h.toHyp52.S_le_normalizer hwS⟩) = 1
    rw [map_mul, map_inv, hcw, inv_mul_cancel]
  have hτR : d.tau ∈ d.R0 := by
    have : d.tau = d.sigma * d.b := by
      show d.tau = d.tau * d.b * d.b
      rw [mul_assoc, d.b_mul_self, mul_one]
    rw [this]
    exact mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left d.b_mem_P)
  have hwZR : w ∈ zpowers d.z ⊔ d.R0 := by
    rw [show w = (c : H) * ((c : H)⁻¹ * w) by group]
    exact mul_mem ((sup_le le_sup_left (zpowers_le.mpr (mem_sup_right hτR))) hcY)
      (mem_sup_right (mem_sup_left hπ))
  have hzR : ∀ x ∈ zpowers d.z, ∀ y ∈ d.R0, x * y = y * x := fun x hx y hy =>
    d.D_comm_R0 F x (zpowers_le.mpr d.z_D hx) y hy
  obtain ⟨u, hu, r, hr, rfl⟩ := Eight.exists_mul_of_mem_sup₂ hzR hwZR
  obtain ⟨y, hyF, hyp, hy1, hya⟩ := d.exists_y_mem_F hSy hB1 hB6 hCF23 hCF24 hCFc hCF1 hCF2 F
  have hTF := (le_sup_right.trans (d.sigma_sup_T_le_F hSy hCF1 hCF2 F) : h.T ≤ h.F32)
  have hbF : d.b ∈ h.F32 := hTF (d.T_eq ▸ mem_sup_right (mem_zpowers _))
  have huS : ∀ v ∈ h.S, u * v = v * u := by
    intro v hv
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hu
    exact (Commute.zpow_left (show Commute d.z v from
      (mem_centralizer_iff.mp d.z_S v hv).symm) k).eq
  have hcomm_r : ∀ v ∈ h.F32, r * v = v * r := by
    intro v hv
    have h2 := hwc v hv
    have h3 : u * (r * v) = u * (v * r) := by
      calc u * (r * v) = u * r * v := (mul_assoc _ _ _).symm
        _ = v * (u * r) := h2
        _ = (v * u) * r := (mul_assoc _ _ _).symm
        _ = (u * v) * r := by rw [huS v (h.F32_le_S hv)]
        _ = u * (v * r) := mul_assoc _ _ _
    exact mul_left_cancel h3
  have hrb := hcomm_r d.b hbF
  have hry := hcomm_r y hyF
  have hσF := d.F32_le_centralizer_sigma hRk hJ hC hB1 hB6 hCF23 hCF24 hCFc hCF1 hCF2 F
  have huz : u ∈ zpowers d.z ⊔ zpowers h.a ⊔ zpowers d.sigma := mem_sup_left (mem_sup_left hu)
  have haM : h.a ∈ zpowers d.z ⊔ zpowers h.a ⊔ zpowers d.sigma :=
    mem_sup_left (mem_sup_right (mem_zpowers _))
  have hσM : d.sigma ∈ zpowers d.z ⊔ zpowers h.a ⊔ zpowers d.sigma :=
    mem_sup_right (mem_zpowers _)
  obtain ⟨π, hπP, hr' | hr'⟩ := d.mem_R0_cases hr
  · subst r
    rcases d.eq_one_or_a_of_comm hπP hrb hyp hy1 hya hry with h2 | h2
    · rw [h2, mul_one]; exact huz
    · rw [h2]; exact mul_mem huz haM
  · subst r
    have hσb := d.sigma_comm_b
    have hσy : d.sigma * y = y * d.sigma := (mem_centralizer_singleton_iff.mp (hσF hyF)).symm
    have hπb : π * d.b = d.b * π := by
      have h3 : π * d.b * d.sigma = d.b * π * d.sigma := by
        calc π * d.b * d.sigma = π * (d.b * d.sigma) := mul_assoc _ _ _
          _ = π * (d.sigma * d.b) := by rw [← hσb]
          _ = π * d.sigma * d.b := (mul_assoc _ _ _).symm
          _ = d.b * (π * d.sigma) := hrb
          _ = d.b * π * d.sigma := (mul_assoc _ _ _).symm
      exact mul_right_cancel h3
    have hπy : π * y = y * π := by
      have h3 : π * y * d.sigma = y * π * d.sigma := by
        calc π * y * d.sigma = π * (y * d.sigma) := mul_assoc _ _ _
          _ = π * (d.sigma * y) := by rw [← hσy]
          _ = π * d.sigma * y := (mul_assoc _ _ _).symm
          _ = y * (π * d.sigma) := hry
          _ = y * π * d.sigma := (mul_assoc _ _ _).symm
      exact mul_right_cancel h3
    rcases d.eq_one_or_a_of_comm hπP hπb hyp hy1 hya hπy with h2 | h2
    · rw [h2, one_mul]; exact mul_mem huz hσM
    · rw [h2]; exact mul_mem huz (mul_mem haM hσM)

theorem x_mem_F (hSy : CFL2Sylow) (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c) (hCFc : CFProp23Center) (hCF1 : CFSec8Simple)
    (hCF2 : CFSec8InnerCentralizer) (F : d.Facts) : h.x ∈ h.F32 := by
  obtain ⟨β, hP⟩ := d.pres
  have hxP : h.x ∈ h.P := (mem_inf.mp H₁.x_mem_P).1
  have hxb : h.x * d.b * h.x⁻¹ = d.p ^ (orderOf d.p / 2) * d.b := by
    rw [d.p_a]; exact d.x_b_x_inv
  obtain ⟨i, hxi, hi4⟩ := hP.zpow_four_of_conj_b hxP (Or.inr hxb)
  have hTF := (le_sup_right.trans (d.sigma_sup_T_le_F hSy hCF1 hCF2 F) : h.T ≤ h.F32)
  have hbF : d.b ∈ h.F32 := hTF (d.T_eq ▸ mem_sup_right (mem_zpowers _))
  have hpi : d.p ^ i ∈ h.F32 := by
    by_cases h4 : orderOf d.p = 4
    · exact zpow_mem (d.p_mem_F_of_four hSy hB1 hB6 hCF23 hCF24 hCFc hCF1 hCF2 F h4) i
    · have h8 := hP.eight_dvd_of_ne_four h4
      rw [← orderOf_dvd_iff_zpow_eq_one] at hi4
      obtain ⟨t, ht⟩ := h8
      obtain ⟨c, hc⟩ := hi4
      rw [ht] at hc
      push_cast at hc
      have hi : i = 2 * ((t : ℤ) * c) := by linarith
      rw [hi, zpow_mul]
      exact zpow_mem (d.zpow_two_mem_F hSy hCF1 hCF2 F) _
  rcases hxi with hx | hx <;> rw [hx]
  · exact hpi
  · exact mul_mem hpi hbF

theorem a_mem_commutator_F (hSy : CFL2Sylow) (hB1 : ConjFixStatement)
    (hB6 : SylowKernelStatement) (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c)
    (hCFc : CFProp23Center) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (F : d.Facts) : h.a ∈ ⁅h.F32, h.F32⁆ := by
  have hTF := (le_sup_right.trans (d.sigma_sup_T_le_F hSy hCF1 hCF2 F) : h.T ≤ h.F32)
  have hbF : d.b ∈ h.F32 := hTF (d.T_eq ▸ mem_sup_right (mem_zpowers _))
  have h1 : ⁅h.x, d.b⁆ = h.a := by
    rw [commutatorElement_def, d.x_b_x_inv, inv_eq_of_mul_eq_one_right d.b_mul_self,
      mul_assoc, d.b_mul_self, mul_one]
  rw [← h1]
  exact commutator_mem_commutator (d.x_mem_F hSy hB1 hB6 hCF23 hCF24 hCFc hCF1 hCF2 F) hbF

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
