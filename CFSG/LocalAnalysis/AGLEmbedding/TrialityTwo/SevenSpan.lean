module

public import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.SevenDim
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

public section

namespace CFSG.AGLEmbedding.TrialityTwo.Seven

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {t : Module.End K V}

section Span

variable [FiniteDimensional K V] (hK : Nat.card K = 2) (h7 : t ^ 7 = 1) (ht : t ≠ 1)
  (hQt : ∀ v, Q (t v) = Q v) (hB : (polarBilin Q).Nondegenerate) (hV : finrank K V = 8)
include hK h7 ht hQt hB hV

theorem span_eq_spU₁ {u : V} (hu : u ∈ spU₁ t) (hu0 : u ≠ 0) :
    Submodule.span K (Set.range ![u, t u, t (t u)]) = spU₁ t := by
  have h2 := two_eq_zero_of_card hK
  set S := Submodule.span K (Set.range ![u, t u, t (t u)]) with hSdef
  have hu1 : t u ∈ spU₁ t := apply_mem_spU₁ hu
  have hu2 : t (t u) ∈ spU₁ t := apply_mem_spU₁ hu1
  have hgen : ∀ i, ![u, t u, t (t u)] i ∈ S := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hSU : S ≤ spU₁ t := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hu
    · exact hu1
    · exact hu2
  have hS : ∀ x ∈ S, t x ∈ S := by
    have hle : S ≤ S.comap t := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact hgen 1
      · exact hgen 2
      · change t (t (t u)) ∈ S
        rw [apply_apply_apply_of_mem_spU₁ h7 h2 hu]
        exact add_mem (hgen 1) (hgen 0)
    exact fun x hx => hle hx
  rcases eq_bot_or_eq_of_le_spU₁ hK h7 ht hQt hB hV hS hSU with h | h
  · exfalso
    apply hu0
    have := hgen 0
    rw [h] at this
    exact (Submodule.mem_bot K).1 this
  · exact h

theorem linearIndependent_of_mem_spU₁ {u : V} (hu : u ∈ spU₁ t) (hu0 : u ≠ 0) :
    LinearIndependent K ![u, t u, t (t u)] := by
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank,
    span_eq_spU₁ hK h7 ht hQt hB hV hu hu0, finrank_spU₁_eq_three hK h7 ht hQt hB hV,
    Fintype.card_fin]

theorem exists_ne_zero_mem_spU₁ : ∃ u ∈ spU₁ t, u ≠ 0 := by
  apply Submodule.exists_mem_ne_zero_of_ne_bot
  intro h
  have := finrank_spU₁_eq_three hK h7 ht hQt hB hV
  rw [h, finrank_bot] at this
  exact absurd this (by norm_num)

end Span

end CFSG.AGLEmbedding.TrialityTwo.Seven
