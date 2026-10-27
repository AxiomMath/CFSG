module
public import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

section OddAdditiveArray

variable {m n : ℕ} [NeZero m] [NeZero n] {a : Fin m → Fin n → ℤ}

theorem eq_add_sub_one_of_exchange (h00 : a 0 0 = 1)
    (hexch : ∀ i j, a i j + a 0 0 = a i 0 + a 0 j) (i : Fin m) (j : Fin n) :
    a i j = a i 0 + a 0 j - 1 := by
  have h := hexch i j
  rw [h00] at h
  omega

theorem odd_of_axes_odd (h00 : a 0 0 = 1)
    (hexch : ∀ i j, a i j + a 0 0 = a i 0 + a 0 j)
    (hrow : ∀ i, Odd (a i 0)) (hcol : ∀ j, Odd (a 0 j)) (i : Fin m) (j : Fin n) :
    Odd (a i j) := by
  rw [eq_add_sub_one_of_exchange h00 hexch i j]
  exact ((hrow i).add_odd (hcol j)).sub_odd odd_one

theorem ne_zero_of_axes_odd (h00 : a 0 0 = 1)
    (hexch : ∀ i j, a i j + a 0 0 = a i 0 + a 0 j)
    (hrow : ∀ i, Odd (a i 0)) (hcol : ∀ j, Odd (a 0 j)) (i : Fin m) (j : Fin n) :
    a i j ≠ 0 := by
  obtain ⟨k, hk⟩ := odd_of_axes_odd h00 hexch hrow hcol i j
  omega

theorem one_le_sq_abs_of_axes_odd (h00 : a 0 0 = 1)
    (hexch : ∀ i j, a i j + a 0 0 = a i 0 + a 0 j)
    (hrow : ∀ i, Odd (a i 0)) (hcol : ∀ j, Odd (a 0 j)) (i : Fin m) (j : Fin n) :
    1 ≤ |a i j| ^ 2 := by
  have h : 1 ≤ |a i j| := Int.one_le_abs (ne_zero_of_axes_odd h00 hexch hrow hcol i j)
  nlinarith

end OddAdditiveArray

section EqualityCase

variable {m n : ℕ} {a : Fin m → Fin n → ℤ}

theorem sq_abs_eq_one_iff (i : Fin m) (j : Fin n) :
    |a i j| ^ 2 = 1 ↔ a i j = 1 ∨ a i j = -1 := by
  rw [sq_abs, sq_eq_one_iff]

end EqualityCase

end CFSG.FeitThompson
