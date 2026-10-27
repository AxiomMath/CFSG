module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.TransportCore

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.EvenSporadicStandard.TwoHS

theorem TwoHSFacts.inv_E {H : Type} [Group H] {E : Subgroup H} {a z b z₁ : H}
    (hE : TwoHS.IsF5Centralizer H E) (hF : TwoHSFacts H a z b z₁) :
    ∀ u ∈ E, u ^ 2 = 1 → u ≠ 1 → u ≠ a →
      ∃ h : H, h * u * h⁻¹ = z ∨ h * u * h⁻¹ = a * z := by
  intro u huE hu2 hu1 hua
  have ha_center : a ∈ center H := by
    rw [hF.center_eq]; exact Subgroup.mem_zpowers a
  have hacomm : ∀ g : H, g * a = a * g := fun g => Subgroup.mem_center_iff.mp ha_center g
  have huord : orderOf u = 2 := orderOf_eq_prime hu2 hu1
  obtain ⟨i, hi⟩ := hF.involution_cover u huord
  have hcomm : E = commutator H := hE.eq_commutator
  fin_cases i
  ·
    rw [isConj_iff] at hi
    obtain ⟨c, hc⟩ := hi
    change c * a * c⁻¹ = u at hc
    exact absurd (hc ▸ (by rw [hacomm c, mul_assoc, mul_inv_cancel, mul_one])) hua
  ·
    rw [isConj_iff] at hi
    obtain ⟨c, hc⟩ := hi
    change c * z * c⁻¹ = u at hc
    exact ⟨c⁻¹, Or.inl (by rw [← hc]; group)⟩
  ·
    rw [isConj_iff] at hi
    obtain ⟨c, hc⟩ := hi
    change c * (a * z) * c⁻¹ = u at hc
    exact ⟨c⁻¹, Or.inr (by rw [← hc]; group)⟩
  ·
    rw [isConj_iff] at hi
    obtain ⟨c, hc⟩ := hi
    change c * b * c⁻¹ = u at hc
    have hmem : c⁻¹ * u * c ∈ E := by
      simpa using hE.normal.conj_mem u huE c⁻¹
    have hbE : b ∈ E := by
      rw [show b = c⁻¹ * u * c by rw [← hc]; group]
      exact hmem
    exact absurd (hcomm ▸ hbE) hF.not_mem_commutator.1
  ·
    rw [isConj_iff] at hi
    obtain ⟨c, hc⟩ := hi
    change c * z₁ * c⁻¹ = u at hc
    have hmem : c⁻¹ * u * c ∈ E := by
      simpa using hE.normal.conj_mem u huE c⁻¹
    have hz₁E : z₁ ∈ E := by
      rw [show z₁ = c⁻¹ * u * c by rw [← hc]; group]
      exact hmem
    exact absurd (hcomm ▸ hz₁E) hF.not_mem_commutator.2

theorem TwoHSFacts.inv_outer {H : Type} [Group H] {E : Subgroup H} {a z b z₁ : H}
    (hE : TwoHS.IsF5Centralizer H E) (hF : TwoHSFacts H a z b z₁) :
    ∀ p : H, p ^ 2 = 1 → p ∉ E → ∃ h : H, h * p * h⁻¹ = b ∨ h * p * h⁻¹ = z₁ := by
  intro p hp2 hpE
  have hp1 : p ≠ 1 := by
    intro h; exact hpE (by simpa [h] using E.one_mem)
  have hpord : orderOf p = 2 := orderOf_eq_prime hp2 hp1
  obtain ⟨i, hi⟩ := hF.involution_cover p hpord
  have hcomm : E = commutator H := hE.eq_commutator
  have haE : a ∈ E := hcomm.symm ▸ hF.mem_commutator.1
  have hzE : z ∈ E := hcomm.symm ▸ hF.mem_commutator.2.1
  have hazE : a * z ∈ E := hcomm.symm ▸ hF.mem_commutator.2.2
  fin_cases i
  · rw [isConj_iff] at hi
    obtain ⟨c, hc⟩ := hi
    change c * a * c⁻¹ = p at hc
    exact absurd (hc ▸ hE.normal.conj_mem a haE c) hpE
  · rw [isConj_iff] at hi
    obtain ⟨c, hc⟩ := hi
    change c * z * c⁻¹ = p at hc
    exact absurd (hc ▸ hE.normal.conj_mem z hzE c) hpE
  · rw [isConj_iff] at hi
    obtain ⟨c, hc⟩ := hi
    change c * (a * z) * c⁻¹ = p at hc
    exact absurd (hc ▸ hE.normal.conj_mem (a * z) hazE c) hpE
  · rw [isConj_iff] at hi
    obtain ⟨c, hc⟩ := hi
    change c * b * c⁻¹ = p at hc
    exact ⟨c⁻¹, Or.inl (by rw [← hc]; group)⟩
  · rw [isConj_iff] at hi
    obtain ⟨c, hc⟩ := hi
    change c * z₁ * c⁻¹ = p at hc
    exact ⟨c⁻¹, Or.inr (by rw [← hc]; group)⟩

end CFSG.EvenSporadicStandard.HNRecog
