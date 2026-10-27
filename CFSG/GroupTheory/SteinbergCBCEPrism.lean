module

public import Mathlib

public section

namespace CFSG.GroupTheory.CartanEilenberg

open Finset

section Prism

variable {X : Type*}

theorem val_succAbove {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    (p.succAbove i : ℕ) = if (i : ℕ) < p then (i : ℕ) else (i : ℕ) + 1 := by
  rcases lt_or_ge (i : ℕ) p with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h), ite_eq_left h]
    rfl
  · rw [Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using h),
      ite_eq_right (by omega)]
    rfl

local macro "prism_close" : tactic =>
  `(tactic| first
    | (exfalso; omega)
    | (congr 1 <;> ext <;> simp only [Fin.val_mk, val_succAbove, Fin.val_succ, Fin.val_castSucc,
        Fin.val_last, Fin.val_zero] <;> split_ifs <;> omega)
    | (congr 2 <;> ext <;> simp only [Fin.val_mk, val_succAbove, Fin.val_succ, Fin.val_castSucc,
        Fin.val_last, Fin.val_zero] <;> split_ifs <;> omega))

end Prism

end CFSG.GroupTheory.CartanEilenberg
