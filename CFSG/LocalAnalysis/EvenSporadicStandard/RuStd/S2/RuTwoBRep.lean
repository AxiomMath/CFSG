module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.Interfaces
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Transport

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup CFSG.EvenSporadicStandard.RuStd

theorem RuTwoBFacts.of_rep {Y : Type} [Group Y] (a : Y)
    (hconj : ∀ u : Y, orderOf u = 2 → Nat.card (centralizer ({u} : Set Y)) = 116480 →
      IsConj a u)
    (h5 : ∃ f ∈ derivedCentralizer a, orderOf f = 5)
    (hu : ∃ u' : Y, orderOf u' = 2 ∧ u' ≠ a ∧
      ∀ x ∈ centralizer ({a} : Set Y), x * u' = u' * x) : RuTwoBFacts Y where
  elt5 u hu2 hc := by
    obtain ⟨c, rfl⟩ := isConj_iff.1 (hconj u hu2 hc)
    obtain ⟨f, hf, hf5⟩ := h5
    refine ⟨c * f * c⁻¹, ?_, ?_⟩
    · have := derivedCentralizer_map (MulAut.conj c) a
      rw [show (MulAut.conj c) a = c * a * c⁻¹ from rfl] at this
      rw [this]
      exact ⟨f, hf, rfl⟩
    · have := (MulAut.conj c).orderOf_eq f
      rw [show (MulAut.conj c) f = c * f * c⁻¹ from rfl] at this
      rw [this, hf5]
  centralInv u hu2 hc := by
    obtain ⟨c, rfl⟩ := isConj_iff.1 (hconj u hu2 hc)
    obtain ⟨u', hu'2, hne, hcomm⟩ := hu
    refine ⟨c * u' * c⁻¹, ?_, ?_, ?_⟩
    · have := (MulAut.conj c).orderOf_eq u'
      rw [show (MulAut.conj c) u' = c * u' * c⁻¹ from rfl] at this
      rw [this, hu'2]
    · intro h
      apply hne
      simpa using h
    · intro x hx
      have h1 := centralizer_singleton_map (MulAut.conj c) a
      rw [show (MulAut.conj c) a = c * a * c⁻¹ from rfl] at h1
      rw [h1] at hx
      obtain ⟨x0, hx0, rfl⟩ := hx
      have := hcomm x0 hx0
      change c * x0 * c⁻¹ * (c * u' * c⁻¹) = c * u' * c⁻¹ * (c * x0 * c⁻¹)
      calc c * x0 * c⁻¹ * (c * u' * c⁻¹) = c * (x0 * u') * c⁻¹ := by group
        _ = c * (u' * x0) * c⁻¹ := by rw [this]
        _ = c * u' * c⁻¹ * (c * x0 * c⁻¹) := by group

end CFSG.EvenSporadicStandard.RuStd.S2
