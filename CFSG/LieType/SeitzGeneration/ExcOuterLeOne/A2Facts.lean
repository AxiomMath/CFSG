module

public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.A2Config

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

public section

namespace CFSG.LieType.SeitzGeneration.ExcOuterLeOne

variable {τ : Tag}

@[expose] def a2Eps (τ : Tag) : Fin 3 → (Fin τ.rank → ℤ) := ![hiRoot τ, delta2 τ, 0]

@[expose] def a2Root (τ : Tag) (i j : Fin 3) : Fin τ.rank → ℤ := a2Eps τ i - a2Eps τ j

theorem a2Root_add (i j l : Fin 3) : a2Root τ i j + a2Root τ j l = a2Root τ i l := by
  simp [a2Root]

theorem a2Root_01 : a2Root τ 0 1 = delta1 τ := by
  simp [a2Root, a2Eps, delta1, delta2]

theorem a2Root_12 : a2Root τ 1 2 = delta2 τ := by
  simp [a2Root, a2Eps]

theorem a2Root_02 : a2Root τ 0 2 = hiRoot τ := by
  simp [a2Root, a2Eps]

theorem a2Root_20 : a2Root τ 2 0 = -hiRoot τ := by
  simp [a2Root, a2Eps]

theorem a2Root_mem (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ∀ i j : Fin 3, i ≠ j → a2Root τ i j ∈ rootFinset τ := by
  rcases hτ with rfl | rfl | rfl | rfl <;> decide +kernel

theorem a2_adj (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ∀ i j k l : Fin 3, (i ≠ j ∧ k ≠ l ∧ ¬(k = j ∧ l = i) ∧ (j = k ∨ i = l)) →
      (a2Root τ i j - a2Root τ k l ∉ rootFinset τ ∧
        a2Root τ i j + (2 : ℕ) • a2Root τ k l ∉ rootFinset τ ∧
        (2 : ℕ) • a2Root τ i j + a2Root τ k l ∉ rootFinset τ ∧
        a2Root τ i j ≠ a2Root τ k l ∧ a2Root τ i j ≠ -a2Root τ k l) := by
  rcases hτ with rfl | rfl | rfl | rfl <;> decide +kernel

theorem a2_far (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ∀ i j k l : Fin 3, (i ≠ j ∧ k ≠ l ∧ j ≠ k ∧ i ≠ l) →
      a2Root τ i j + a2Root τ k l ∉ rootFinset τ ∧ a2Root τ i j + a2Root τ k l ≠ 0 := by
  rcases hτ with rfl | rfl | rfl | rfl <;> decide +kernel

end CFSG.LieType.SeitzGeneration.ExcOuterLeOne
