module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L53E

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
include h

theorem sq_eq_one_of_mul {q r : G} (hq : q ∈ Q) (hr : r ∈ S ⊓ L)
    (hqr : q * r * (q * r) = 1) : q * q = 1 ∧ r * r = 1 := by
  have hc := h.commute_Q_R hq hr
  have h1 : q * q * (r * r) = 1 := by
    rw [← hqr, show q * r * (q * r) = q * (r * q) * r by group, ← hc]; group
  have hqq : q * q = 1 := by
    have h2 : q * q ∈ Q ⊓ L := by
      refine mem_inf.mpr ⟨mul_mem hq hq, ?_⟩
      rw [eq_inv_of_mul_eq_one_left h1]
      exact inv_mem (mul_mem (mem_inf.mp hr).2 (mem_inf.mp hr).2)
    rw [h.Q_inf_L, mem_bot] at h2
    exact h2
  refine ⟨hqq, ?_⟩
  rw [hqq, one_mul] at h1
  exact h1

theorem isConj_mul_t {q r : G} (hq : q ∈ Q) (hr : r ∈ S ⊓ L) (hr2 : orderOf r = 2) :
    IsConj (q * r) (q * t) := by
  obtain ⟨k, -, hkC, hk⟩ := h.exists_conj_t_footeF h.zQ h.z2 h.isPGroup_Q le_rfl
    (fun x hx => h.S_le_centralizer (h.QS hx)) hr hr2
  have hkq : k⁻¹ * q * k = q := by
    have h2 := mem_centralizer_iff.mp hkC q hq
    calc k⁻¹ * q * k = k⁻¹ * (q * k) := by group
      _ = k⁻¹ * (k * q) := by rw [h2]
      _ = q := by group
  refine isConj_iff.mpr ⟨k⁻¹, ?_⟩
  rw [inv_inv, show k⁻¹ * (q * r) * k = k⁻¹ * q * k * (k⁻¹ * r * k) by group, hkq, hk]

theorem exists_center_conj (hgood : ∀ w ∈ Q, orderOf w = 2 → Good53 S L Q w) {q : G}
    (hq : q ∈ Q) (hq2 : orderOf q = 2) :
    ∃ q' ∈ Q, (∀ s ∈ S, s * q' = q' * s) ∧ IsConj q q' ∧ IsConj (q * t) (q' * t) := by
  obtain ⟨g, hgR, hgQ, hgZ⟩ := hgood q hq hq2
  have htR : g⁻¹ * t * g ∈ S ⊓ L := conj_mem_of_mem_normalizer hgR h.tR
  have ht2 : orderOf (g⁻¹ * t * g) = 2 := by
    rw [show g⁻¹ * t * g = g⁻¹ * t * g⁻¹⁻¹ by rw [inv_inv], orderOf_conj', h.t2]
  have h1 : IsConj (q * t) (g⁻¹ * q * g * (g⁻¹ * t * g)) := isConj_iff.mpr ⟨g⁻¹, by
    rw [inv_inv]; group⟩
  exact ⟨g⁻¹ * q * g, hgQ, hgZ, isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]⟩,
    h1.trans (h.isConj_mul_t hgQ htR ht2)⟩

theorem mul_t_center {q : G} (hqZ : ∀ s ∈ S, s * q = q * s) :
    ∀ s ∈ S, s * (q * t) = q * t * s := fun s hs => by
  rw [← mul_assoc, hqZ s hs, mul_assoc, h.tZ s hs, mul_assoc]

theorem conj_mem_Q_of_mem_QR (hgood : ∀ w ∈ Q, orderOf w = 2 → Good53 S L Q w)
    (hQ51 : ∀ u ∈ Q, (∀ s ∈ S, s * u = u * s) → ∀ y, (∀ s ∈ S, s * y = y * s) →
      IsConj u y → y ∈ Q)
    {w y q r : G} (hwQ : w ∈ Q) (hw2 : orderOf w = 2) (hwy : IsConj w y) (hq : q ∈ Q)
    (hr : r ∈ S ⊓ L) (hy : y = q * r) : r = 1 := by
  by_contra hr1
  have hw22 : w * w = 1 := by rw [← sq, ← hw2, pow_orderOf_eq_one]
  have hyy : q * r * (q * r) = 1 := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hwy
    rw [← hy, ← hc, show c * w * c⁻¹ * (c * w * c⁻¹) = c * (w * w) * c⁻¹ by group, hw22]
    group
  obtain ⟨hqq, hrr⟩ := h.sq_eq_one_of_mul hq hr hyy
  have hwqt : IsConj w (q * t) :=
    hwy.trans (hy ▸ h.isConj_mul_t hq hr (orderOf_eq_prime (by rw [sq]; exact hrr) hr1))
  obtain ⟨g, -, hgQ, hgZ⟩ := hgood w hwQ hw2
  have hww' : IsConj (g⁻¹ * w * g) w := isConj_iff.mpr ⟨g, by group⟩
  by_cases hq1 : q = 1
  · rw [hq1, one_mul] at hwqt
    exact h.t_not_mem_Q (hQ51 _ hgQ hgZ t h.tZ (hww'.trans hwqt))
  · obtain ⟨q', hq'Q, hq'Z, -, hc⟩ :=
      h.exists_center_conj hgood hq (orderOf_eq_prime (by rw [sq]; exact hqq) hq1)
    have h1 := hQ51 _ hgQ hgZ _ (h.mul_t_center hq'Z) (hww'.trans (hwqt.trans hc))
    exact h.t_not_mem_Q (by
      rw [show t = q'⁻¹ * (q' * t) by group]; exact mul_mem (inv_mem hq'Q) h1)

theorem conj_t_mem_R_of_mem_QR (hgood : ∀ w ∈ Q, orderOf w = 2 → Good53 S L Q w)
    (ht51 : ∀ y, (∀ s ∈ S, s * y = y * s) → IsConj t y → y ∈ S ⊓ L) {y q r : G}
    (hty : IsConj t y) (hq : q ∈ Q) (hr : r ∈ S ⊓ L) (hy : y = q * r) : q = 1 := by
  by_contra hq1
  have ht22 : t * t = 1 := by rw [← sq, ← h.t2, pow_orderOf_eq_one]
  have hyy : q * r * (q * r) = 1 := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hty
    rw [← hy, ← hc, show c * t * c⁻¹ * (c * t * c⁻¹) = c * (t * t) * c⁻¹ by group, ht22]
    group
  obtain ⟨hqq, hrr⟩ := h.sq_eq_one_of_mul hq hr hyy
  obtain ⟨q', hq'Q, hq'Z, hqq', hc⟩ :=
    h.exists_center_conj hgood hq (orderOf_eq_prime (by rw [sq]; exact hqq) hq1)
  have hq'1 : q' ≠ 1 := fun h1 => hq1 (by rw [h1] at hqq'; exact isConj_one_left.mp hqq')
  by_cases hr1 : r = 1
  · rw [hy, hr1, mul_one] at hty
    have h1 := ht51 _ hq'Z (hty.trans hqq')
    have h2 : q' ∈ Q ⊓ L := mem_inf.mpr ⟨hq'Q, (mem_inf.mp h1).2⟩
    rw [h.Q_inf_L, mem_bot] at h2
    exact hq'1 h2
  · have htqt : IsConj t (q * t) :=
      hty.trans (hy ▸ h.isConj_mul_t hq hr (orderOf_eq_prime (by rw [sq]; exact hrr) hr1))
    have h1 := ht51 _ (h.mul_t_center hq'Z) (htqt.trans hc)
    have h2 : q' ∈ Q ⊓ L := mem_inf.mpr ⟨hq'Q, by
      rw [show q' = q' * t * t⁻¹ by group]; exact mul_mem (mem_inf.mp h1).2 (inv_mem h.tL)⟩
    rw [h.Q_inf_L, mem_bot] at h2
    exact hq'1 h2

end Sec5

end CFSG.ComponentClassification.Foote5

