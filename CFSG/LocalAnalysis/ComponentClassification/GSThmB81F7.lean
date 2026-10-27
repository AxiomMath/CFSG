module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81F6

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable (d : Data H₁)

theorem le_F_of_four_group (hSy : CFL2Sylow) (hCF1 : CFSec8Simple)
    (hCF2 : CFSec8InnerCentralizer) (F : d.Facts) {T' : Subgroup H} (hT'P : T' ≤ h.P)
    (hT'2 : ∀ w ∈ T', w * w = 1) (hT'4 : Nat.card T' = 4)
    (hσT : ∀ w ∈ T', d.sigma * w = w * d.sigma) : T' ≤ h.F32 := by
  obtain ⟨i, hiD, hi2, hi1, hiz, hc⟩ := d.exists_four_group hSy F
  obtain ⟨h4, hsq⟩ := card_sup_zpowers_of_inv hi2 d.z_mul_self hi1 d.z_ne_one hiz hc
  set V := zpowers i ⊔ zpowers d.z with hV
  have hVD : V ≤ h.D := sup_le (zpowers_le.mpr hiD) (zpowers_le.mpr d.z_D)
  have hσ2 := d.sigma_mul_self
  have hcT : ∀ x ∈ zpowers d.sigma, ∀ y ∈ T', x * y = y * x := by
    intro x hx y hy
    rcases eq_one_or_of_mem_zpowers_of_mul_self hσ2 hx with h1 | h1
    · rw [h1, one_mul, mul_one]
    · rw [h1]; exact hσT y hy
  have hd : zpowers d.sigma ⊓ T' = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hw1, hw2⟩ := mem_inf.mp hw
    rcases eq_one_or_of_mem_zpowers_of_mul_self hσ2 hw1 with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hT'P hw2) (d.sigma_not_mem_P hCF1 hCF2 F)
  have hσ1 : d.sigma ≠ 1 := fun h1 => d.sigma_not_mem_P hCF1 hCF2 F (h1 ▸ one_mem _)
  have hcσ : Nat.card (zpowers d.sigma) = 2 := by
    rw [Nat.card_zpowers]; exact orderOf_eq_prime (by rw [pow_two]; exact hσ2) hσ1
  have hR : zpowers d.sigma ⊔ T' ≤ d.R0 :=
    sup_le (zpowers_le.mpr (mem_sup_right (mem_zpowers _))) (hT'P.trans le_sup_left)
  have hc8 : Nat.card ↥(zpowers d.sigma ⊔ T') = 8 := by
    rw [Seven.card_sup_of_commute hcT hd, hcσ, hT'4]
  have hsq8 : ∀ w ∈ zpowers d.sigma ⊔ T', w * w = 1 := by
    refine Seven.sup_sq_eq_one (fun w hw => ?_) hT'2 hcT
    rcases eq_one_or_of_mem_zpowers_of_mul_self hσ2 hw with h1 | h1
    · rw [h1, one_mul]
    · rw [h1]; exact hσ2
  have hcV : ∀ x ∈ V, ∀ y ∈ zpowers d.sigma ⊔ T', x * y = y * x :=
    fun x hx y hy => d.D_comm_R0 F x (hVD hx) y (hR hy)
  have hdV : V ⊓ (zpowers d.sigma ⊔ T') = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf hVD hR).trans (d.D_inf_R0 hCF1 hCF2 F).le)
  have hE : V ⊔ (zpowers d.sigma ⊔ T') ≤ h.F32 := by
    refine Eight.le_JeN (sup_le (hVD.trans h.toHyp52.D_le_S) (hR.trans d.R0_le_S))
      (Seven.sup_sq_eq_one hsq hsq8 hcV) ?_
    rw [Seven.card_sup_of_commute hcV hdV, h4, hc8]
  exact le_sup_right.trans (le_sup_right.trans hE)

theorem zpow_two_ne (h8 : 8 ∣ orderOf d.p) :
    d.p ^ (2 : ℤ) ≠ 1 ∧ d.p ^ (2 : ℤ) ≠ h.a := by
  obtain ⟨β, hP⟩ := d.pres
  have hn := d.four_le_orderOf_p
  constructor
  · intro h1
    have := orderOf_le_of_pow_eq_one (by norm_num) (by rwa [← zpow_natCast] : d.p ^ (2 : ℕ) = 1)
    obtain ⟨t, ht⟩ := h8
    omega
  · intro h1
    rw [← d.p_a] at h1
    have h2 : d.p ^ (2 : ℤ) * d.p ^ (2 : ℤ) = 1 := by rw [h1]; exact hP.a_mul_a
    rw [← zpow_add] at h2
    have := orderOf_le_of_pow_eq_one (by norm_num) (by rwa [← zpow_natCast] : d.p ^ (4 : ℕ) = 1)
    obtain ⟨t, ht⟩ := h8
    omega

theorem p_mem_F_of_four (hSy : CFL2Sylow) (hB1 : ConjFixStatement)
    (hB6 : SylowKernelStatement) (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c)
    (hCFc : CFProp23Center) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) (F : d.Facts)
    (h4 : orderOf d.p = 4) : d.p ∈ h.F32 := by
  obtain ⟨β, hP⟩ := d.pres
  rcases d.sigma_p hB1 hB6 hCF23 hCF24 hCFc hCF1 hCF2 F with hσp | hσp
  · have hβ : β = -1 := by
      rcases hP.beta with hβ | hβ
      · exact hβ
      · exfalso
        apply hP.noncomm
        have h1 : d.b * d.p * d.b⁻¹ = d.p := by
          rw [hP.rel, hβ, h4]
          norm_num
        calc d.b * d.p = d.b * d.p * d.b⁻¹ * d.b := by group
          _ = d.p * d.b := by rw [h1]
    have hpb2 : d.p * d.b * (d.p * d.b) = 1 := by
      have := hP.sq_zpow_mul_b 1
      rw [hβ, zpow_one] at this
      rw [this]
      simp
    have hσ : ∀ w ∈ d.R0, d.sigma * w = w * d.sigma := fun w hw =>
      d.sigma_comm_R0_of_comm hσp hw
    have hpbP : d.p * d.b ∈ h.P := mul_mem d.p_mem d.b_mem_P
    have hpbp : d.p * d.b ∉ zpowers d.p := by
      have := hP.zpow_mul_b_not_mem 1
      rwa [zpow_one] at this
    have ha1 : h.a ≠ 1 := a_ne_one' (h := h)
    have hapb : h.a ≠ d.p * d.b := fun h1 => hpbp (h1 ▸ (d.p_a ▸ pow_mem (mem_zpowers _) _))
    have hpba : h.a * (d.p * d.b) = d.p * d.b * h.a := by
      have hap : d.p ^ (orderOf d.p / 2) * d.p = d.p * d.p ^ (orderOf d.p / 2) := by
        rw [← pow_succ, ← pow_succ']
      rw [← d.p_a]
      calc d.p ^ (orderOf d.p / 2) * (d.p * d.b) = (d.p ^ (orderOf d.p / 2) * d.p) * d.b := by
            group
        _ = d.p * (d.p ^ (orderOf d.p / 2) * d.b) := by rw [hap]; group
        _ = d.p * (d.b * d.p ^ (orderOf d.p / 2)) := by rw [hP.a_comm_b]
        _ = d.p * d.b * d.p ^ (orderOf d.p / 2) := by group
    have hpb1 : d.p * d.b ≠ 1 := fun h1 => hpbp (h1 ▸ one_mem _)
    obtain ⟨hc4, hsq⟩ := card_sup_zpowers_of_inv (Six.a_mul_a_self h.toHyp52) hpb2 ha1 hpb1
      hapb hpba
    have hT' := d.le_F_of_four_group hSy hCF1 hCF2 F
      (sup_le (zpowers_le.mpr h.toHyp52.a_mem_P) (zpowers_le.mpr hpbP)) hsq hc4
      (fun w hw => hσ w (mem_sup_left ((sup_le (zpowers_le.mpr h.toHyp52.a_mem_P)
        (zpowers_le.mpr hpbP)) hw)))
    have hTF := (le_sup_right.trans (d.sigma_sup_T_le_F hSy hCF1 hCF2 F) : h.T ≤ h.F32)
    have hbF : d.b ∈ h.F32 := hTF (d.T_eq ▸ mem_sup_right (mem_zpowers _))
    have := mul_mem (hT' (mem_sup_right (mem_zpowers _))) (inv_mem hbF)
    rwa [mul_inv_cancel_right] at this
  · exfalso
    have := d.eight_dvd_of_sigma_ne hB1 hB6 hCF23 hCF24 hCFc hCF1 hCF2 F hσp
    omega

theorem exists_y_mem_F (hSy : CFL2Sylow) (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c) (hCFc : CFProp23Center) (hCF1 : CFSec8Simple)
    (hCF2 : CFSec8InnerCentralizer) (F : d.Facts) :
    ∃ y ∈ h.F32, y ∈ zpowers d.p ∧ y ≠ 1 ∧ y ≠ h.a := by
  obtain ⟨β, hP⟩ := d.pres
  by_cases h4 : orderOf d.p = 4
  · refine ⟨d.p, d.p_mem_F_of_four hSy hB1 hB6 hCF23 hCF24 hCFc hCF1 hCF2 F h4, mem_zpowers _,
      fun h1 => ?_, fun h1 => ?_⟩
    · rw [h1, orderOf_one] at h4; omega
    · have h2 : d.p = d.p ^ (orderOf d.p / 2) := h1.trans d.p_a.symm
      rw [h4, show (4 : ℕ) / 2 = 2 by norm_num, pow_two] at h2
      have h3 : d.p = 1 := by
        have : d.p * d.p = d.p * 1 := by rw [mul_one]; exact h2.symm
        exact mul_left_cancel this
      rw [h3, orderOf_one] at h4
      omega
  · have h8 := hP.eight_dvd_of_ne_four h4
    obtain ⟨h1, h2⟩ := d.zpow_two_ne h8
    exact ⟨d.p ^ (2 : ℤ), d.zpow_two_mem_F hSy hCF1 hCF2 F, zpow_mem (mem_zpowers _) _, h1, h2⟩

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
