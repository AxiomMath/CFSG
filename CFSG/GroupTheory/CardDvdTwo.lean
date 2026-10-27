module

public import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

public section

namespace CFSG.GroupTheory

theorem eq_of_ne_one_of_card_dvd_two {A : Type*} [Group A] (hA : Nat.card A ∣ 2) {a b : A}
    (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  by_contra hne
  have hpos : Nat.card A ≠ 0 := by
    rintro h0
    rw [h0] at hA
    exact absurd hA (by decide)
  have hfin : Finite A := Nat.finite_of_card_ne_zero hpos
  have hinj : Function.Injective (![1, a, b] : Fin 3 → A) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hne, Ne.symm ha, Ne.symm hb, Ne.symm hne] at hij ⊢
  have h3 : 3 ≤ Nat.card A := by
    simpa using @Nat.card_le_card_of_injective (Fin 3) A hfin _ hinj
  have h2 : Nat.card A ≤ 2 := Nat.le_of_dvd (by decide) hA
  exact Nat.not_succ_le_self 2 (le_trans h3 h2)

end CFSG.GroupTheory
