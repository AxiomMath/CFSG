module

public import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.SevenBasis

public section

namespace CFSG.AGLEmbedding.TrialityTwo.Seven

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {t : Module.End K V}

namespace Frame

variable (F : Frame Q t)

abbrev e (k : Fin 3) : V := F.b (.inl k.castSucc)

abbrev f (k : Fin 3) : V := F.b (.inr k.castSucc)

theorem polar_e_f (i j : Fin 3) : polar Q (F.e i) (F.f j) = if i = j then 1 else 0 := by
  rw [F.polar_lr]
  simp only [Fin.castSucc_inj]

end Frame

section Coord

variable [FiniteDimensional K V] (hV : finrank K V = 2 * 4) (h7 : t ^ 7 = 1) (h2 : (2 : K) = 0)
  (hQt : ∀ v, Q (t v) = Q v) (F : Frame Q t)
include hV h7 h2 hQt

theorem eq_sum_of_mem_spU₁ {x : V} (hx : x ∈ spU₁ t) :
    x = ∑ k : Fin 3, polar Q x (F.f k) • F.e k := by
  have h := eq_sum_of_hyp F.polar_lr F.polar_ll F.polar_rr hV x
  have hl : ∀ i, polar Q x (F.b (.inl i)) = 0 := by
    intro i
    induction i using Fin.lastCases with
    | last => rw [polar_comm]; exact polar_eq_zero_of_mem_fixC_of_mem_spU₁ hQt h7 h2 F.mem_C₁ hx
    | cast i => exact polar_eq_zero_of_mem_spU₁ hQt h7 h2 hx (F.mem_U₁ i)
  have hw : polar Q x (F.b (.inr (Fin.last 3))) = 0 := by
    rw [polar_comm]
    exact polar_eq_zero_of_mem_fixC_of_mem_spU₁ hQt h7 h2 F.mem_C₂ hx
  simp only [hl, zero_smul, Finset.sum_const_zero, add_zero] at h
  rw [Fin.sum_univ_castSucc, hw, zero_smul, add_zero] at h
  exact h

theorem eq_sum_of_mem_spU₂ {y : V} (hy : y ∈ spU₂ t) :
    y = ∑ k : Fin 3, polar Q y (F.e k) • F.f k := by
  have h := eq_sum_of_hyp F.polar_lr F.polar_ll F.polar_rr hV y
  have hr : ∀ i, polar Q y (F.b (.inr i)) = 0 := by
    intro i
    induction i using Fin.lastCases with
    | last => rw [polar_comm]; exact polar_eq_zero_of_mem_fixC_of_mem_spU₂ hQt h7 h2 F.mem_C₂ hy
    | cast i => exact polar_eq_zero_of_mem_spU₂ hQt h7 h2 hy (F.mem_U₂ i)
  have hw : polar Q y (F.b (.inl (Fin.last 3))) = 0 := by
    rw [polar_comm]
    exact polar_eq_zero_of_mem_fixC_of_mem_spU₂ hQt h7 h2 F.mem_C₁ hy
  simp only [hr, zero_smul, Finset.sum_const_zero, zero_add] at h
  rw [Fin.sum_univ_castSucc, hw, zero_smul, add_zero] at h
  exact h

end Coord

end CFSG.AGLEmbedding.TrialityTwo.Seven
