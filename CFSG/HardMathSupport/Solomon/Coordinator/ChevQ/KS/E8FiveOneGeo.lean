module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSE8Five

namespace One

theorem geometric_of_ratio {K : Type} [Field K] (δ : Fin 5 → K) (hδ : ∀ i, δ i ≠ 0)
    (h : ∀ i j : Fin 5, i ≠ j → δ (i + 1) * δ j = δ i * δ (j + 1)) :
    ∃ lam : K, lam ^ 5 = 1 ∧ ∀ i : Fin 5, δ i = δ 0 * lam ^ (i : ℕ) := by
  have h0 : δ 0 ≠ 0 := hδ 0
  obtain ⟨lam, hd1⟩ : ∃ lam : K, δ 1 = lam * δ 0 :=
    ⟨δ 1 / δ 0, (div_mul_cancel₀ (δ 1) h0).symm⟩
  have hstep : ∀ i : Fin 5, δ (i + 1) = lam * δ i := by
    intro i
    by_cases hi : i = 0
    · subst hi
      exact hd1
    · have hh : δ (i + 1) * δ 0 = δ i * δ 1 := h i 0 hi
      rw [hd1] at hh
      apply mul_right_cancel₀ h0
      linear_combination hh
  have g2 : δ 2 = lam * δ 1 := hstep 1
  have g3 : δ 3 = lam * δ 2 := hstep 2
  have g4 : δ 4 = lam * δ 3 := hstep 3
  have g0 : δ 0 = lam * δ 4 := hstep 4
  have f1 : δ 1 = δ 0 * lam ^ 1 := by linear_combination hd1
  have f2 : δ 2 = δ 0 * lam ^ 2 := by linear_combination g2 + lam * f1
  have f3 : δ 3 = δ 0 * lam ^ 3 := by linear_combination g3 + lam * f2
  have f4 : δ 4 = δ 0 * lam ^ 4 := by linear_combination g4 + lam * f3
  have hlam5 : lam ^ 5 = 1 := by
    apply mul_left_cancel₀ h0
    linear_combination -g0 - lam * f4
  refine ⟨lam, hlam5, ?_⟩
  intro i
  fin_cases i
  · simp
  · exact f1
  · exact f2
  · exact f3
  · exact f4

end One

end KSE8Five

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
