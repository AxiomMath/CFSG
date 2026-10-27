module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Out1SlimSylow

public section

namespace CFSG.EvenSporadicStandard.Solomon78

variable {Y : Type} [Group Y]

@[expose] def ConjCommutes (u a : Y) : Prop :=
  ∃ h : Y, (h * u * h⁻¹) * a = a * (h * u * h⁻¹)

theorem ConjCommutes.of_isConj {u a : Y} (h : IsConj u a) : ConjCommutes u a := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  exact ⟨c, by rw [hc]⟩

theorem ConjCommutes.of_commute {u a : Y} (h : u * a = a * u) : ConjCommutes u a :=
  ⟨1, by simpa using h⟩

theorem ConjCommutes.symm {u a : Y} (h : ConjCommutes u a) : ConjCommutes a u := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c⁻¹, ?_⟩
  calc c⁻¹ * a * c⁻¹⁻¹ * u = c⁻¹ * (a * (c * u * c⁻¹)) * c := by group
    _ = c⁻¹ * ((c * u * c⁻¹) * a) * c := by rw [hc]
    _ = u * (c⁻¹ * a * c⁻¹⁻¹) := by group

theorem ConjCommutes.congr_left {u u' a : Y} (hu : IsConj u u') (h : ConjCommutes u' a) :
    ConjCommutes u a := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hu
  obtain ⟨h₁, hh₁⟩ := h
  refine ⟨h₁ * c, ?_⟩
  have e : h₁ * c * u * (h₁ * c)⁻¹ = h₁ * u' * h₁⁻¹ := by rw [← hc]; group
  rw [e]
  exact hh₁

theorem ConjCommutes.congr_right {u a a' : Y} (ha : IsConj a a') (h : ConjCommutes u a') :
    ConjCommutes u a :=
  (ConjCommutes.congr_left ha h.symm).symm

theorem involutionsCommute_of_conjCommutes
    (h : ∀ u a : Y, orderOf u = 2 → orderOf a = 2 → ConjCommutes u a) : InvolutionsCommute Y :=
  h

end CFSG.EvenSporadicStandard.Solomon78
