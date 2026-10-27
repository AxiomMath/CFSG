module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81D
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81Fus3
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB8Je

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

theorem card_sup_zpowers_of_inv {G : Type} [Group G] [Finite G] {x y : G} (hx : x * x = 1)
    (hy : y * y = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x ≠ y) (hc : x * y = y * x) :
    Nat.card ↥(zpowers x ⊔ zpowers y) = 4 ∧ ∀ w ∈ zpowers x ⊔ zpowers y, w * w = 1 := by
  have hcx : Nat.card (zpowers x) = 2 := by
    rw [Nat.card_zpowers]; exact orderOf_eq_prime (by rw [pow_two]; exact hx) hx1
  have hcy : Nat.card (zpowers y) = 2 := by
    rw [Nat.card_zpowers]; exact orderOf_eq_prime (by rw [pow_two]; exact hy) hy1
  have hcW : ∀ u ∈ zpowers x, ∀ v ∈ zpowers y, u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hu
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hv
    exact (Commute.zpow_zpow hc i j).eq
  have hd : zpowers x ⊓ zpowers y = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hw1, hw2⟩ := mem_inf.mp hw
    rcases Hyp59.L81Hyp.Data.eq_one_or_of_mem_zpowers_of_mul_self hx hw1 with h1 | h1
    · exact h1
    · rcases Hyp59.L81Hyp.Data.eq_one_or_of_mem_zpowers_of_mul_self hy hw2 with h2 | h2
      · exact h2
      · exact absurd (h1.symm.trans h2) hxy
  refine ⟨by rw [Seven.card_sup_of_commute hcW hd, hcx, hcy], ?_⟩
  refine Seven.sup_sq_eq_one (fun w hw => ?_) (fun w hw => ?_) hcW
  · rcases Hyp59.L81Hyp.Data.eq_one_or_of_mem_zpowers_of_mul_self hx hw with h1 | h1
    · rw [h1, one_mul]
    · rw [h1]; exact hx
  · rcases Hyp59.L81Hyp.Data.eq_one_or_of_mem_zpowers_of_mul_self hy hw with h1 | h1
    · rw [h1, one_mul]
    · rw [h1]; exact hy

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

abbrev F32 (h : Hyp59 H) : Subgroup H := Eight.JeN 32 h.S

theorem F32_le_S (h : Hyp59 H) : h.F32 ≤ h.S := Eight.JeN_le 32 h.S

theorem normalizer_S_le_normalizer_F32 (h : Hyp59 H) :
    normalizer (h.S : Set H) ≤ normalizer (h.F32 : Set H) :=
  Eight.normalizer_le_normalizer_JeN 32 h.S

theorem S_le_normalizer_F32 (h : Hyp59 H) : h.S ≤ normalizer (h.F32 : Set H) :=
  le_normalizer.trans h.normalizer_S_le_normalizer_F32

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable (d : Data H₁)


theorem sigma_not_mem_P (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) (F : d.Facts) :
    d.sigma ∉ h.P := by
  intro hσ
  apply d.tau_not_mem_DP hCF1 hCF2 F
  have : d.tau = d.sigma * d.b := by
    show d.tau = d.tau * d.b * d.b
    rw [mul_assoc, d.b_mul_self, mul_one]
  rw [this]
  exact mem_sup_right (mul_mem hσ d.b_mem_P)

include d in
theorem T_mul_self : ∀ w ∈ h.T, w * w = 1 := by
  intro w hw
  rcases h.mem_T_cases d.b_ord d.T_eq d.a_comm_b hw with h1 | h1 | h1 | h1 <;> rw [h1]
  · rw [one_mul]
  · exact Six.a_mul_a_self h.toHyp52
  · exact d.b_mul_self
  · rw [show h.a * d.b * (h.a * d.b) = h.a * (d.b * h.a) * d.b by group, ← d.a_comm_b,
      show h.a * (h.a * d.b) * d.b = (h.a * h.a) * (d.b * d.b) by group,
      Six.a_mul_a_self h.toHyp52, d.b_mul_self, one_mul]

theorem sigma_sup_T (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) (F : d.Facts) :
    zpowers d.sigma ⊔ h.T ≤ d.R0 ∧ Nat.card ↥(zpowers d.sigma ⊔ h.T) = 8 ∧
      ∀ w ∈ zpowers d.sigma ⊔ h.T, w * w = 1 := by
  have hσ2 := d.sigma_mul_self
  have hσa : d.sigma * h.a = h.a * d.sigma := by
    rw [sigma, mul_assoc, ← d.a_comm_b, ← mul_assoc, d.tau_comm_a, mul_assoc]
  have hcT : ∀ x ∈ zpowers d.sigma, ∀ y ∈ h.T, x * y = y * x := by
    intro x hx y hy
    rcases eq_one_or_of_mem_zpowers_of_mul_self hσ2 hx with h1 | h1
    · rw [h1, one_mul, mul_one]
    · rw [h1]
      rcases h.mem_T_cases d.b_ord d.T_eq d.a_comm_b hy with h2 | h2 | h2 | h2 <;> rw [h2]
      · rw [one_mul, mul_one]
      · exact hσa
      · exact d.sigma_comm_b
      · rw [← mul_assoc, hσa, mul_assoc, d.sigma_comm_b, mul_assoc]
  have hd : zpowers d.sigma ⊓ h.T = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hw1, hw2⟩ := mem_inf.mp hw
    rcases eq_one_or_of_mem_zpowers_of_mul_self hσ2 hw1 with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ (mem_inf.mp hw2).2) (d.sigma_not_mem_P hCF1 hCF2 F)
  have hσ1 : d.sigma ≠ 1 := fun h1 => d.sigma_not_mem_P hCF1 hCF2 F (h1 ▸ one_mem _)
  have hcσ : Nat.card (zpowers d.sigma) = 2 := by
    rw [Nat.card_zpowers]; exact orderOf_eq_prime (by rw [pow_two]; exact hσ2) hσ1
  refine ⟨sup_le (zpowers_le.mpr (mem_sup_right (mem_zpowers _)))
    ((inf_le_right : h.T ≤ h.P).trans le_sup_left), ?_, ?_⟩
  · rw [Seven.card_sup_of_commute hcT hd, hcσ, d.T_card]
  · refine Seven.sup_sq_eq_one (fun w hw => ?_) (T_mul_self d) hcT
    rcases eq_one_or_of_mem_zpowers_of_mul_self hσ2 hw with h1 | h1
    · rw [h1, one_mul]
    · rw [h1]; exact hσ2

theorem card_E0 (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) (F : d.Facts)
    {V : Subgroup H} (hVD : V ≤ h.D) (hV2 : ∀ w ∈ V, w * w = 1) (hV4 : Nat.card V = 4) :
    V ⊔ (zpowers d.sigma ⊔ h.T) ≤ h.S ∧ (∀ w ∈ V ⊔ (zpowers d.sigma ⊔ h.T), w * w = 1) ∧
      Nat.card ↥(V ⊔ (zpowers d.sigma ⊔ h.T)) = 32 := by
  obtain ⟨hle, hc8, hsq⟩ := d.sigma_sup_T hCF1 hCF2 F
  have hc : ∀ x ∈ V, ∀ y ∈ zpowers d.sigma ⊔ h.T, x * y = y * x :=
    fun x hx y hy => d.D_comm_R0 F x (hVD hx) y (hle hy)
  have hd : V ⊓ (zpowers d.sigma ⊔ h.T) = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf hVD hle).trans (d.D_inf_R0 hCF1 hCF2 F).le)
  refine ⟨sup_le (hVD.trans h.toHyp52.D_le_S) (hle.trans d.R0_le_S),
    Seven.sup_sq_eq_one hV2 hsq hc, ?_⟩
  rw [Seven.card_sup_of_commute hc hd, hV4, hc8]

theorem E0_le_F (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) (F : d.Facts)
    {V : Subgroup H} (hVD : V ≤ h.D) (hV2 : ∀ w ∈ V, w * w = 1) (hV4 : Nat.card V = 4) :
    V ⊔ (zpowers d.sigma ⊔ h.T) ≤ h.F32 := by
  obtain ⟨hS, hsq, hc⟩ := d.card_E0 hCF1 hCF2 F hVD hV2 hV4
  exact Eight.le_JeN hS hsq hc

theorem exists_four_group (hSy : CFL2Sylow) (F : d.Facts) :
    ∃ i ∈ h.D, i * i = 1 ∧ i ≠ 1 ∧ i ≠ d.z ∧ i * d.z = d.z * i := by
  obtain ⟨i, hiD, hi2, e, heD, hie⟩ := d.exists_noncentral_inv hSy F
  have hzc : ∀ w ∈ h.D, w * d.z = d.z * w := fun w hw =>
    mem_centralizer_iff.mp d.z_S w (h.toHyp52.D_le_S hw)
  refine ⟨i, hiD, hi2, fun h1 => hie (by rw [h1, one_mul, mul_one]), fun h1 => hie ?_,
    hzc i hiD⟩
  rw [h1]
  exact (hzc e heD).symm

theorem sigma_sup_T_le_F (hSy : CFL2Sylow) (hCF1 : CFSec8Simple)
    (hCF2 : CFSec8InnerCentralizer) (F : d.Facts) : zpowers d.sigma ⊔ h.T ≤ h.F32 := by
  obtain ⟨i, hiD, hi2, hi1, hiz, hc⟩ := d.exists_four_group hSy F
  obtain ⟨h4, hsq⟩ := card_sup_zpowers_of_inv hi2 d.z_mul_self hi1 d.z_ne_one hiz hc
  exact le_sup_right.trans (d.E0_le_F hCF1 hCF2 F
    (sup_le (zpowers_le.mpr hiD) (zpowers_le.mpr d.z_D)) hsq h4)

theorem inv_mem_F (hSy : CFL2Sylow) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (F : d.Facts) {w : H} (hwD : w ∈ h.D) (hw2 : w * w = 1) : w ∈ h.F32 := by
  by_cases hw1 : w = 1
  · rw [hw1]; exact one_mem _
  have hzc : w * d.z = d.z * w := mem_centralizer_iff.mp d.z_S w (h.toHyp52.D_le_S hwD)
  by_cases hwz : w = d.z
  · obtain ⟨i, hiD, hi2, hi1, hiz, hc⟩ := d.exists_four_group hSy F
    obtain ⟨h4, hsq⟩ := card_sup_zpowers_of_inv hi2 d.z_mul_self hi1 d.z_ne_one hiz hc
    exact d.E0_le_F hCF1 hCF2 F (sup_le (zpowers_le.mpr hiD) (zpowers_le.mpr d.z_D)) hsq h4
      (mem_sup_left (mem_sup_right (by rw [hwz]; exact mem_zpowers _)))
  · obtain ⟨h4, hsq⟩ := card_sup_zpowers_of_inv hw2 d.z_mul_self hw1 d.z_ne_one hwz hzc
    exact d.E0_le_F hCF1 hCF2 F (sup_le (zpowers_le.mpr hwD) (zpowers_le.mpr d.z_D)) hsq h4
      (mem_sup_left (mem_sup_left (mem_zpowers _)))

theorem D_le_F (hSy : CFL2Sylow) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (F : d.Facts) : h.D ≤ h.F32 := by
  intro e he
  obtain ⟨-, hprod⟩ := d.D_facts hSy F
  obtain ⟨i, hiD, j, hjD, hi, hj, rfl⟩ := hprod e he
  exact mul_mem (d.inv_mem_F hSy hCF1 hCF2 F hiD hi) (d.inv_mem_F hSy hCF1 hCF2 F hjD hj)

theorem zpow_two_mem_F (hSy : CFL2Sylow) (hCF1 : CFSec8Simple)
    (hCF2 : CFSec8InnerCentralizer) (F : d.Facts) : d.p ^ (2 : ℤ) ∈ h.F32 := by
  obtain ⟨β, hP⟩ := d.pres
  have hTF := (le_sup_right.trans (d.sigma_sup_T_le_F hSy hCF1 hCF2 F) : h.T ≤ h.F32)
  have hbF : d.b ∈ h.F32 := hTF (d.T_eq ▸ mem_sup_right (mem_zpowers _))
  have haF : h.a ∈ h.F32 := hTF (d.T_eq ▸ mem_sup_left (mem_zpowers _))
  have hpS : d.p ∈ h.S := (mem_inf.mp d.p_mem).1
  have hpbF : d.p * d.b * d.p⁻¹ ∈ h.F32 :=
    (mem_normalizer_iff.mp (h.S_le_normalizer_F32 hpS) d.b).mp hbF
  have hbp : d.p * d.b * d.p⁻¹ * d.b⁻¹ = d.p ^ (1 - β) := by
    rw [show d.p * d.b * d.p⁻¹ * d.b⁻¹ = d.p * (d.b * d.p ^ (-1 : ℤ) * d.b⁻¹) by
      rw [zpow_neg_one]; group, hP.conj_zpow, ← zpow_one_add]
    congr 1
    ring
  have hc : d.p * d.b * d.p⁻¹ * d.b⁻¹ ∈ h.F32 := mul_mem hpbF (inv_mem hbF)
  rcases hP.zpow_two_eq hbp with h1 | h1
  · rw [h1]; exact hc
  · rw [h1, d.p_a]; exact mul_mem hc haF

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
