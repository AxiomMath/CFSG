module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB8MaxClass
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81Fus1

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

theorem two_pow_orderOf_p : ∃ k : ℕ, orderOf d.p = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 h.P := h.toHyp52.isPGroup_S.to_le inf_le_left
  obtain ⟨k, hk⟩ := hP2 ⟨d.p, d.p_mem⟩
  have h1 : d.p ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1)
  exact ⟨j, hj⟩

theorem four_le_orderOf_p : 4 ≤ orderOf d.p := by
  have h1 := d.card_P
  have h2 := H₁.eight_le
  omega

theorem exists_beta : ∃ β : ℤ, d.r * d.p * d.r⁻¹ = d.p ^ β ∧
    (β = -1 ∨ β = (orderOf d.p : ℤ) / 2 - 1) := by
  rcases d.rel with h1 | h1
  · exact ⟨-1, by rw [h1, zpow_neg_one], Or.inl rfl⟩
  · refine ⟨((orderOf d.p / 2 - 1 : ℕ) : ℤ), by rw [h1, zpow_natCast], Or.inr ?_⟩
    have := d.four_le_orderOf_p
    omega

theorem r_not_mem : d.r ∉ zpowers d.p := by
  intro hr
  have hle : h.P ≤ zpowers d.p := by
    rw [← d.P_cl, closure_le]
    intro w hw
    rcases hw with rfl | rfl
    · exact mem_zpowers _
    · exact hr
  have h1 := card_le_of_le hle
  rw [Nat.card_zpowers, ← d.card_P] at h1
  have := d.four_le_orderOf_p
  omega

theorem r_noncomm : d.r * d.p ≠ d.p * d.r := by
  intro hc
  apply d.r_not_mem
  rw [← d.C_p]
  exact mem_inf.mpr ⟨d.r_mem, mem_centralizer_singleton_iff.mpr hc⟩

theorem r_mul_self : d.r * d.r = 1 := by rw [← pow_two]; exact d.r_sq

theorem pres_r : ∃ β : ℤ, Eight.MC.Pres h.P d.p d.r β := by
  obtain ⟨β, hβ, hβ'⟩ := d.exists_beta
  exact ⟨β, ⟨d.p_mem, d.r_mem, d.r_not_mem, d.r_mul_self, d.card_P, d.four_le_orderOf_p,
    d.two_pow_orderOf_p, hβ, hβ', d.r_noncomm⟩⟩

theorem b_not_mem_zpowers : d.b ∉ zpowers d.p := by
  intro hb
  obtain ⟨β, hP⟩ := d.pres_r
  rcases hP.eq_one_or_a hb d.b_mul_self with h1 | h1
  · have := d.b_ord
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  · rw [d.p_a] at h1
    apply Six.a_not_mem_B H₁.C_eq
    rw [← h1]
    exact d.b_mem_B

theorem pres : ∃ β : ℤ, Eight.MC.Pres h.P d.p d.b β := by
  obtain ⟨β, hP⟩ := d.pres_r
  refine ⟨β, ⟨d.p_mem, d.b_mem_P, d.b_not_mem_zpowers, d.b_mul_self, d.card_P,
    d.four_le_orderOf_p, d.two_pow_orderOf_p, ?_, hP.beta, ?_⟩⟩
  · obtain ⟨i, hi | hi⟩ := hP.mem_cases d.b_mem_P
    · exact absurd (hi ▸ zpow_mem (mem_zpowers _) i) d.b_not_mem_zpowers
    · rw [hi, show d.p ^ i * d.r * d.p * (d.p ^ i * d.r)⁻¹ =
          d.p ^ i * (d.r * d.p * d.r⁻¹) * (d.p ^ i)⁻¹ by group, hP.rel, ← zpow_add,
        ← zpow_neg, ← zpow_add]
      congr 1
      ring
  · intro hc
    apply d.b_not_mem_zpowers
    rw [← d.C_p]
    exact mem_inf.mpr ⟨d.b_mem_P, mem_centralizer_singleton_iff.mpr hc⟩

abbrev sigma : H := d.tau * d.b

theorem sigma_mem_S : d.sigma ∈ h.S := mul_mem d.tau_mem_S d.b_mem_S

theorem sigma_mul_self : d.sigma * d.sigma = 1 := by
  rw [sigma, show d.tau * d.b * (d.tau * d.b) = d.tau * (d.b * d.tau) * d.b by group,
    ← d.tau_comm_b, show d.tau * (d.tau * d.b) * d.b = (d.tau * d.tau) * (d.b * d.b) by group,
    d.tau_sq, d.b_mul_self, one_mul]

theorem sigma_comm_b : d.sigma * d.b = d.b * d.sigma := by
  rw [sigma, show d.b * (d.tau * d.b) = (d.b * d.tau) * d.b by group, ← d.tau_comm_b]

theorem conj_mem_zpowers {s : H} (hs : s ∈ h.S) {y : H} (hy : y ∈ zpowers d.p) :
    s * y * s⁻¹ ∈ zpowers d.p := by
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
  have h1 : (MulAut.conj s) (d.p ^ i) = ((MulAut.conj s) d.p) ^ i := map_zpow _ d.p i
  simp only [MulAut.conj_apply] at h1
  rw [h1]
  exact zpow_mem (d.S_p s hs) i

theorem exists_sigma_comm (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c) (hCFc : CFProp23Center) (hCF1 : CFSec8Simple)
    (hCF2 : CFSec8InnerCentralizer) (F : d.Facts) :
    ∃ i : ℤ, d.p ^ (4 * i) = 1 ∧ d.p ^ (2 * i) ≠ 1 ∧ d.sigma * d.p ^ i = d.p ^ i * d.sigma := by
  obtain ⟨β, hP⟩ := d.pres
  have hxP : h.x ∈ h.P := (mem_inf.mp H₁.x_mem_P).1
  have hxb : h.x * d.b * h.x⁻¹ = d.p ^ (orderOf d.p / 2) * d.b := by
    rw [d.p_a]; exact d.x_b_x_inv
  obtain ⟨i, hxi, hi4⟩ := hP.zpow_four_of_conj_b hxP (Or.inr hxb)
  have htx := d.tau_x hB1 hB6 hCF23 hCF24 hCFc hCF1 hCF2 F
  have hτb := d.tau_comm_b
  have hτx : ¬ (d.tau * h.x = h.x * d.tau) := by
    intro hc
    have : h.x⁻¹ * d.tau * h.x = d.tau := by rw [mul_assoc, hc]; group
    rw [this] at htx
    apply a_ne_one' (h := h)
    calc h.a = h.a * d.tau * d.tau⁻¹ := by group
      _ = 1 := by rw [← htx, mul_inv_cancel]
  have hnot : ¬ (d.tau * d.p ^ i = d.p ^ i * d.tau) := by
    intro hc
    apply hτx
    rcases hxi with hx | hx
    · rw [hx]; exact hc
    · rw [hx, ← mul_assoc, hc, mul_assoc, hτb, ← mul_assoc]
  have hymem : d.p ^ i ∈ zpowers d.p := zpow_mem (mem_zpowers _) i
  have hy2 : d.p ^ i * d.p ^ i = d.p ^ (orderOf d.p / 2) := by
    have h1 : d.p ^ i * d.p ^ i * (d.p ^ i * d.p ^ i) = 1 := by
      rw [← zpow_add, ← zpow_add]
      rw [show i + i + (i + i) = 4 * i by ring, hi4]
    rcases hP.eq_one_or_a (mul_mem hymem hymem) h1 with h2 | h2
    · exfalso
      rcases hP.eq_one_or_a hymem h2 with h3 | h3
      · apply hnot; rw [h3]; group
      · apply hnot
        rw [h3, d.p_a]
        exact d.tau_comm_a
    · exact h2
  have hi2 : d.p ^ (2 * i) ≠ 1 := by
    rw [two_mul, zpow_add, hy2]
    exact hP.a_ne_one
  refine ⟨i, hi4, hi2, ?_⟩
  have haτ : d.tau * d.p ^ (orderOf d.p / 2) * d.tau⁻¹ = d.p ^ (orderOf d.p / 2) := by
    rw [d.p_a, d.tau_comm_a]; group
  have hτy : d.tau * d.p ^ i * d.tau⁻¹ = (d.p ^ i)⁻¹ := by
    have hmem := d.conj_mem_zpowers d.tau_mem_S hymem
    have hsq : d.tau * d.p ^ i * d.tau⁻¹ * (d.tau * d.p ^ i * d.tau⁻¹) =
        d.p ^ (orderOf d.p / 2) := by
      rw [show d.tau * d.p ^ i * d.tau⁻¹ * (d.tau * d.p ^ i * d.tau⁻¹) =
        d.tau * (d.p ^ i * d.p ^ i) * d.tau⁻¹ by group, hy2, haτ]
    rcases hP.eq_or_eq_inv_of_sq_eq_a hymem hmem hy2 hsq with h1 | h1
    · exfalso
      apply hnot
      calc d.tau * d.p ^ i = d.tau * d.p ^ i * d.tau⁻¹ * d.tau := by group
        _ = d.p ^ i * d.tau := by rw [h1]
    · exact h1
  have hby : d.b * d.p ^ i * d.b⁻¹ = (d.p ^ i)⁻¹ := by
    have hmem : d.b * d.p ^ i * d.b⁻¹ ∈ zpowers d.p := by
      rw [hP.conj_zpow]; exact zpow_mem (mem_zpowers _) _
    have hsq : d.b * d.p ^ i * d.b⁻¹ * (d.b * d.p ^ i * d.b⁻¹) = d.p ^ (orderOf d.p / 2) := by
      rw [show d.b * d.p ^ i * d.b⁻¹ * (d.b * d.p ^ i * d.b⁻¹) =
        d.b * (d.p ^ i * d.p ^ i) * d.b⁻¹ by group, hy2, hP.conj_a]
    rcases hP.eq_or_eq_inv_of_sq_eq_a hymem hmem hy2 hsq with h1 | h1
    · exfalso
      have h2 : d.b * d.p ^ i = d.p ^ i * d.b := by
        calc d.b * d.p ^ i = d.b * d.p ^ i * d.b⁻¹ * d.b := by group
          _ = d.p ^ i * d.b := by rw [h1]
      rcases (hP.comm_b_iff hymem).mp h2 with h3 | h3
      · apply hi2; rw [two_mul, zpow_add, h3, one_mul]
      · apply hi2
        rw [two_mul, zpow_add, h3, hP.a_mul_a]
    · exact h1
  calc d.sigma * d.p ^ i = d.tau * (d.b * d.p ^ i * d.b⁻¹) * d.b := by rw [sigma]; group
    _ = d.tau * (d.p ^ i)⁻¹ * d.tau⁻¹ * (d.tau * d.b) := by rw [hby]; group
    _ = (d.tau * d.p ^ i * d.tau⁻¹)⁻¹ * d.sigma := by group
    _ = d.p ^ i * d.sigma := by rw [hτy, inv_inv]

theorem sigma_p (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement) (hCF23 : CFProp23Fusion)
    (hCF24 : CFProp24c) (hCFc : CFProp23Center) (hCF1 : CFSec8Simple)
    (hCF2 : CFSec8InnerCentralizer) (F : d.Facts) :
    d.sigma * d.p * d.sigma⁻¹ = d.p ∨ d.sigma * d.p * d.sigma⁻¹ = h.a * d.p := by
  obtain ⟨β, hP⟩ := d.pres
  obtain ⟨i, hi4, hi2, hσy⟩ := d.exists_sigma_comm hB1 hB6 hCF23 hCF24 hCFc hCF1 hCF2 F
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (d.S_p _ d.sigma_mem_S)
  rcases hP.conj_eq_or_of_comm d.sigma_mul_self hk.symm hi4 hi2 hσy with h1 | h1
  · exact Or.inl h1
  · right
    rw [h1, d.p_a]

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
