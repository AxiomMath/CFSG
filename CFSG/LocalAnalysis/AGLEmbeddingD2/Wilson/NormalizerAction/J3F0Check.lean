module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3F0Mat

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Matrix

theorem matChk_true : matChk = true := by decide +kernel

theorem matFacts :
    (1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) ∈ matS ∧ (∀ i : Fin 6, actMat i ∈ matS) ∧
    (∀ s ∈ matS, ∀ t ∈ matS, s * t ∈ matS) ∧ (∀ s ∈ matS, ∃ t ∈ matS, s * t = 1) ∧
    (∀ s ∈ matS, s = 1 ∨ ∃ v : Fin 4 → ZMod 3, (s - 1) *ᵥ ((s - 1) *ᵥ v) ≠ 0) := by
  have h := matChk_true
  simp only [matChk, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, Bool.or_eq_true,
    List.mem_finRange, forall_const, inS_iff, eqM_iff, nzV_iff, mulM_eq, mulV_eq, subOne_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, h3, h4, ?_⟩
  intro s hs
  rcases h5 s hs with h | ⟨v, -, hv⟩
  · exact Or.inl h
  · exact Or.inr ⟨v, hv⟩

theorem fix_triv (a : Fin 4 → ZMod 3) (h1 : actMat 1 *ᵥ a = a) (h2 : actMat 2 *ᵥ a = a) :
    a 0 = 0 ∧ a 1 = 0 ∧ a 2 = 0 := by
  have key : ∀ a : Fin 4 → ZMod 3, mulV (actMat 1) a = a → mulV (actMat 2) a = a →
      a 0 = 0 ∧ a 1 = 0 ∧ a 2 = 0 := by decide
  exact key a (by rw [mulV_eq]; exact h1) (by rw [mulV_eq]; exact h2)

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
