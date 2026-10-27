module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Equiv

private lemma perm_comm_apply {τ g : Perm (Fin 8)} (h : τ * g = g * τ) (i : Fin 8) :
    τ (g i) = g (τ i) :=
  congrArg (fun f : Perm (Fin 8) => f i) h

theorem cent_perm_four {σ : Perm (Fin 8)}
    (hσ : ∀ g ∈ alternatingGroup (Fin 8),
      g * (swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7) =
        (swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7) * g → σ * g = g * σ) :
    σ = 1 ∨ σ = swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7 := by
  let s : Perm (Fin 8) := swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7
  have hg1 : (swap 0 1 * swap 2 3 : Perm (Fin 8)) ∈ alternatingGroup (Fin 8) := by
    rw [Equiv.Perm.mem_alternatingGroup]; simp
  have hg4 : (swap 0 2 * swap 1 3 : Perm (Fin 8)) ∈ alternatingGroup (Fin 8) := by
    rw [Equiv.Perm.mem_alternatingGroup]; simp
  have hg5 : (swap 2 4 * swap 3 5 : Perm (Fin 8)) ∈ alternatingGroup (Fin 8) := by
    rw [Equiv.Perm.mem_alternatingGroup]; simp
  have hg6 : (swap 4 6 * swap 5 7 : Perm (Fin 8)) ∈ alternatingGroup (Fin 8) := by
    rw [Equiv.Perm.mem_alternatingGroup]; simp
  have hc1 : (swap 0 1 * swap 2 3 : Perm (Fin 8)) * s =
      s * (swap 0 1 * swap 2 3) := by decide
  have hc4 : (swap 0 2 * swap 1 3 : Perm (Fin 8)) * s =
      s * (swap 0 2 * swap 1 3) := by decide
  have hc5 : (swap 2 4 * swap 3 5 : Perm (Fin 8)) * s =
      s * (swap 2 4 * swap 3 5) := by decide
  have hc6 : (swap 4 6 * swap 5 7 : Perm (Fin 8)) * s =
      s * (swap 4 6 * swap 5 7) := by decide
  have h1 : σ 1 = (swap 0 1 * swap 2 3 : Perm (Fin 8)) (σ 0) := by
    have := perm_comm_apply (hσ (swap 0 1 * swap 2 3) hg1 hc1) 0
    rwa [show (swap 0 1 * swap 2 3 : Perm (Fin 8)) 0 = 1 by decide] at this
  have h2 : σ 2 = (swap 0 2 * swap 1 3 : Perm (Fin 8)) (σ 0) := by
    have := perm_comm_apply (hσ (swap 0 2 * swap 1 3) hg4 hc4) 0
    rwa [show (swap 0 2 * swap 1 3 : Perm (Fin 8)) 0 = 2 by decide] at this
  have h3 : σ 3 = (swap 0 2 * swap 1 3 : Perm (Fin 8)) (σ 1) := by
    have := perm_comm_apply (hσ (swap 0 2 * swap 1 3) hg4 hc4) 1
    rwa [show (swap 0 2 * swap 1 3 : Perm (Fin 8)) 1 = 3 by decide] at this
  have h4 : σ 4 = (swap 2 4 * swap 3 5 : Perm (Fin 8)) (σ 2) := by
    have := perm_comm_apply (hσ (swap 2 4 * swap 3 5) hg5 hc5) 2
    rwa [show (swap 2 4 * swap 3 5 : Perm (Fin 8)) 2 = 4 by decide] at this
  have h5 : σ 5 = (swap 2 4 * swap 3 5 : Perm (Fin 8)) (σ 3) := by
    have := perm_comm_apply (hσ (swap 2 4 * swap 3 5) hg5 hc5) 3
    rwa [show (swap 2 4 * swap 3 5 : Perm (Fin 8)) 3 = 5 by decide] at this
  have h6 : σ 6 = (swap 4 6 * swap 5 7 : Perm (Fin 8)) (σ 4) := by
    have := perm_comm_apply (hσ (swap 4 6 * swap 5 7) hg6 hc6) 4
    rwa [show (swap 4 6 * swap 5 7 : Perm (Fin 8)) 4 = 6 by decide] at this
  have h7 : σ 7 = (swap 4 6 * swap 5 7 : Perm (Fin 8)) (σ 5) := by
    have := perm_comm_apply (hσ (swap 4 6 * swap 5 7) hg6 hc6) 5
    rwa [show (swap 4 6 * swap 5 7 : Perm (Fin 8)) 5 = 7 by decide] at this
  obtain ⟨v, hv⟩ : ∃ v : Fin 8, σ 0 = v := ⟨σ 0, rfl⟩
  fin_cases v
  ·
    have hv0 : σ 0 = 0 := by rw [hv]; decide
    rw [show (swap 0 1 * swap 2 3 : Perm (Fin 8)) (σ 0) = 1 by rw [hv]; decide] at h1
    rw [show (swap 0 2 * swap 1 3 : Perm (Fin 8)) (σ 0) = 2 by rw [hv]; decide] at h2
    rw [h1, show (swap 0 2 * swap 1 3 : Perm (Fin 8)) 1 = 3 by decide] at h3
    rw [h2, show (swap 2 4 * swap 3 5 : Perm (Fin 8)) 2 = 4 by decide] at h4
    rw [h3, show (swap 2 4 * swap 3 5 : Perm (Fin 8)) 3 = 5 by decide] at h5
    rw [h4, show (swap 4 6 * swap 5 7 : Perm (Fin 8)) 4 = 6 by decide] at h6
    rw [h5, show (swap 4 6 * swap 5 7 : Perm (Fin 8)) 5 = 7 by decide] at h7
    left
    refine Equiv.ext (fun i => ?_)
    fin_cases i
    · exact hv0.trans (by decide)
    · exact h1.trans (by decide)
    · exact h2.trans (by decide)
    · exact h3.trans (by decide)
    · exact h4.trans (by decide)
    · exact h5.trans (by decide)
    · exact h6.trans (by decide)
    · exact h7.trans (by decide)
  ·
    have hv1 : σ 0 = 1 := by rw [hv]; decide
    rw [show (swap 0 1 * swap 2 3 : Perm (Fin 8)) (σ 0) = 0 by rw [hv]; decide] at h1
    rw [show (swap 0 2 * swap 1 3 : Perm (Fin 8)) (σ 0) = 3 by rw [hv]; decide] at h2
    rw [h1, show (swap 0 2 * swap 1 3 : Perm (Fin 8)) 0 = 2 by decide] at h3
    rw [h2, show (swap 2 4 * swap 3 5 : Perm (Fin 8)) 3 = 5 by decide] at h4
    rw [h3, show (swap 2 4 * swap 3 5 : Perm (Fin 8)) 2 = 4 by decide] at h5
    rw [h4, show (swap 4 6 * swap 5 7 : Perm (Fin 8)) 5 = 7 by decide] at h6
    rw [h5, show (swap 4 6 * swap 5 7 : Perm (Fin 8)) 4 = 6 by decide] at h7
    right
    refine Equiv.ext (fun i => ?_)
    fin_cases i
    · exact hv1.trans (by decide)
    · exact h1.trans (by decide)
    · exact h2.trans (by decide)
    · exact h3.trans (by decide)
    · exact h4.trans (by decide)
    · exact h5.trans (by decide)
    · exact h6.trans (by decide)
    · exact h7.trans (by decide)
  ·
    rw [show (swap 0 2 * swap 1 3 : Perm (Fin 8)) (σ 0) = 0 by rw [hv]; decide] at h2
    rw [h2, show (swap 2 4 * swap 3 5 : Perm (Fin 8)) 0 = 0 by decide] at h4
    exact absurd (σ.injective (h2.trans h4.symm)) (by decide)
  ·
    rw [show (swap 0 2 * swap 1 3 : Perm (Fin 8)) (σ 0) = 1 by rw [hv]; decide] at h2
    rw [h2, show (swap 2 4 * swap 3 5 : Perm (Fin 8)) 1 = 1 by decide] at h4
    exact absurd (σ.injective (h2.trans h4.symm)) (by decide)
  ·
    have hfix : (swap 0 1 * swap 2 3 : Perm (Fin 8)) (σ 0) = σ 0 := by rw [hv]; decide
    exact absurd (σ.injective (h1.trans hfix)) (by decide)
  ·
    have hfix : (swap 0 1 * swap 2 3 : Perm (Fin 8)) (σ 0) = σ 0 := by rw [hv]; decide
    exact absurd (σ.injective (h1.trans hfix)) (by decide)
  ·
    have hfix : (swap 0 1 * swap 2 3 : Perm (Fin 8)) (σ 0) = σ 0 := by rw [hv]; decide
    exact absurd (σ.injective (h1.trans hfix)) (by decide)
  ·
    have hfix : (swap 0 1 * swap 2 3 : Perm (Fin 8)) (σ 0) = σ 0 := by rw [hv]; decide
    exact absurd (σ.injective (h1.trans hfix)) (by decide)

end CFSG.EvenSporadicStandard.HNRecog.Section4
