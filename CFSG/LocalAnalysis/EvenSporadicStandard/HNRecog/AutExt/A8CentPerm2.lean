module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Equiv

private lemma mem_alt_mul_swap (a b c d : Fin 8) (hab : a ≠ b) (hcd : c ≠ d) :
    (swap a b * swap c d : Perm (Fin 8)) ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab,
    Equiv.Perm.sign_swap hcd, Int.units_mul_self]

private lemma four_eq_four {σ : Perm (Fin 8)}
    (e14 : σ 5 = (swap 4 5 * swap 5 6 : Perm (Fin 8)) (σ 4))
    (e15 : σ 6 = (swap 4 5 * swap 5 6 : Perm (Fin 8)) (σ 5))
    (e26 : σ 7 = (swap 5 6 * swap 6 7 : Perm (Fin 8)) (σ 6))
    (n0 : σ 4 ≠ 0) (n1 : σ 4 ≠ 1) (n2 : σ 4 ≠ 2) (n3 : σ 4 ≠ 3) :
    σ 4 = 4 := by
  have aux : ∀ w : Fin 8, σ 4 = w → w = 4 := by
    intro w hw
    fin_cases w
    · exact absurd hw n0
    · exact absurd hw n1
    · exact absurd hw n2
    · exact absurd hw n3
    · rfl
    · have ha : σ 5 = 6 := by rw [e14, hw]; decide
      exact absurd (σ.injective (show σ 7 = σ 6 from by rw [e26, e15, ha]; decide)) (by decide)
    · have ha : σ 5 = 4 := by rw [e14, hw]; decide
      have hb : σ 6 = 5 := by rw [e15, ha]; decide
      exact absurd (σ.injective (show σ 7 = σ 4 from by rw [e26, hb, hw]; decide)) (by decide)
    · exact absurd (σ.injective (show σ 5 = σ 4 from by rw [e14, hw]; decide)) (by decide)
  exact aux (σ 4) rfl

theorem cent_perm_two_two {σ : Perm (Fin 8)}
    (hσ : ∀ g ∈ alternatingGroup (Fin 8),
      g * (swap 0 1 * swap 2 3) = (swap 0 1 * swap 2 3) * g → σ * g = g * σ) :
    σ = 1 ∨ σ = swap 0 1 * swap 2 3 := by
  have h3 : σ * (swap 0 1 * swap 4 5) = (swap 0 1 * swap 4 5) * σ :=
    hσ _ (mem_alt_mul_swap 0 1 4 5 (by decide) (by decide)) (by decide)
  have h5 : σ * (swap 0 2 * swap 1 3) = (swap 0 2 * swap 1 3) * σ :=
    hσ _ (mem_alt_mul_swap 0 2 1 3 (by decide) (by decide)) (by decide)
  have h1 : σ * (swap 4 5 * swap 5 6) = (swap 4 5 * swap 5 6) * σ :=
    hσ _ (mem_alt_mul_swap 4 5 5 6 (by decide) (by decide)) (by decide)
  have h2 : σ * (swap 5 6 * swap 6 7) = (swap 5 6 * swap 6 7) * σ :=
    hσ _ (mem_alt_mul_swap 5 6 6 7 (by decide) (by decide)) (by decide)
  have key : ∀ g : Perm (Fin 8), σ * g = g * σ → ∀ i, σ (g i) = g (σ i) := by
    intro g hg i
    simpa [Equiv.Perm.mul_apply] using congrArg (fun f : Perm (Fin 8) => f i) hg
  have e30 : σ 1 = (swap 0 1 * swap 4 5 : Perm (Fin 8)) (σ 0) := by
    have h := key (swap 0 1 * swap 4 5) h3 0
    rwa [show (swap 0 1 * swap 4 5 : Perm (Fin 8)) (0 : Fin 8) = 1 by decide] at h
  have e50 : σ 2 = (swap 0 2 * swap 1 3 : Perm (Fin 8)) (σ 0) := by
    have h := key (swap 0 2 * swap 1 3) h5 0
    rwa [show (swap 0 2 * swap 1 3 : Perm (Fin 8)) (0 : Fin 8) = 2 by decide] at h
  have e51 : σ 3 = (swap 0 2 * swap 1 3 : Perm (Fin 8)) (σ 1) := by
    have h := key (swap 0 2 * swap 1 3) h5 1
    rwa [show (swap 0 2 * swap 1 3 : Perm (Fin 8)) (1 : Fin 8) = 3 by decide] at h
  have e14 : σ 5 = (swap 4 5 * swap 5 6 : Perm (Fin 8)) (σ 4) := by
    have h := key (swap 4 5 * swap 5 6) h1 4
    rwa [show (swap 4 5 * swap 5 6 : Perm (Fin 8)) (4 : Fin 8) = 5 by decide] at h
  have e15 : σ 6 = (swap 4 5 * swap 5 6 : Perm (Fin 8)) (σ 5) := by
    have h := key (swap 4 5 * swap 5 6) h1 5
    rwa [show (swap 4 5 * swap 5 6 : Perm (Fin 8)) (5 : Fin 8) = 6 by decide] at h
  have e26 : σ 7 = (swap 5 6 * swap 6 7 : Perm (Fin 8)) (σ 6) := by
    have h := key (swap 5 6 * swap 6 7) h2 6
    rwa [show (swap 5 6 * swap 6 7 : Perm (Fin 8)) (6 : Fin 8) = 7 by decide] at h
  have h01 : σ 0 = 0 ∨ σ 0 = 1 := by
    have aux : ∀ v : Fin 8, σ 0 = v → v = 0 ∨ v = 1 := by
      intro v hv
      fin_cases v
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd (σ.injective (show σ 1 = σ 0 from by rw [e30, hv]; decide)) (by decide)
      · exact absurd (σ.injective (show σ 1 = σ 0 from by rw [e30, hv]; decide)) (by decide)
      · exact absurd (σ.injective (show σ 2 = σ 0 from by rw [e50, hv]; decide)) (by decide)
      · exact absurd (σ.injective (show σ 2 = σ 0 from by rw [e50, hv]; decide)) (by decide)
      · exact absurd (σ.injective (show σ 2 = σ 0 from by rw [e50, hv]; decide)) (by decide)
      · exact absurd (σ.injective (show σ 2 = σ 0 from by rw [e50, hv]; decide)) (by decide)
    exact aux (σ 0) rfl
  rcases h01 with h0 | h0
  · have h1v : σ 1 = 1 := by rw [e30, h0]; decide
    have h2v : σ 2 = 2 := by rw [e50, h0]; decide
    have h3v : σ 3 = 3 := by rw [e51, h1v]; decide
    have n0 : σ 4 ≠ 0 := fun h =>
      absurd (σ.injective (show σ 4 = σ 0 from by rw [h, h0])) (by decide)
    have n1 : σ 4 ≠ 1 := fun h =>
      absurd (σ.injective (show σ 4 = σ 1 from by rw [h, h1v])) (by decide)
    have n2 : σ 4 ≠ 2 := fun h =>
      absurd (σ.injective (show σ 4 = σ 2 from by rw [h, h2v])) (by decide)
    have n3 : σ 4 ≠ 3 := fun h =>
      absurd (σ.injective (show σ 4 = σ 3 from by rw [h, h3v])) (by decide)
    have h4 : σ 4 = 4 := four_eq_four e14 e15 e26 n0 n1 n2 n3
    have h5v : σ 5 = 5 := by rw [e14, h4]; decide
    have h6v : σ 6 = 6 := by rw [e15, h5v]; decide
    have h7v : σ 7 = 7 := by rw [e26, h6v]; decide
    left
    ext i
    fin_cases i <;> simp_all [Equiv.swap_apply_def]
  · have h1v : σ 1 = 0 := by rw [e30, h0]; decide
    have h2v : σ 2 = 3 := by rw [e50, h0]; decide
    have h3v : σ 3 = 2 := by rw [e51, h1v]; decide
    have n0 : σ 4 ≠ 0 := fun h =>
      absurd (σ.injective (show σ 4 = σ 1 from by rw [h, h1v])) (by decide)
    have n1 : σ 4 ≠ 1 := fun h =>
      absurd (σ.injective (show σ 4 = σ 0 from by rw [h, h0])) (by decide)
    have n2 : σ 4 ≠ 2 := fun h =>
      absurd (σ.injective (show σ 4 = σ 3 from by rw [h, h3v])) (by decide)
    have n3 : σ 4 ≠ 3 := fun h =>
      absurd (σ.injective (show σ 4 = σ 2 from by rw [h, h2v])) (by decide)
    have h4 : σ 4 = 4 := four_eq_four e14 e15 e26 n0 n1 n2 n3
    have h5v : σ 5 = 5 := by rw [e14, h4]; decide
    have h6v : σ 6 = 6 := by rw [e15, h5v]; decide
    have h7v : σ 7 = 7 := by rw [e26, h6v]; decide
    right
    ext i
    fin_cases i <;> simp_all [Equiv.swap_apply_def]

end CFSG.EvenSporadicStandard.HNRecog.Section4
