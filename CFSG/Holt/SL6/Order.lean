module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsL64

public section

namespace CFSG.Holt.SL6

open scoped MatrixGroups

theorem two_mul_card_ne_factorial {m : ℕ} (hm : 2 ≤ m) :
    2 * Nat.card SL(6, ZMod 2) ≠ (2 * m).factorial := by
  rw [CFSG.EvenSmallLie.UnitarySix.YamadaInputs.card_SL_six_two,
    CFSG.EvenSmallLie.UnitarySix.YamadaEnd.orderSL62]
  intro h
  rcases le_or_gt m 6 with h6 | h7
  · have h1 := Nat.factorial_le (show 2 * m ≤ 12 by omega)
    have h12 : Nat.factorial 12 = 479001600 := by decide
    omega
  · have h1 := Nat.factorial_le (show 14 ≤ 2 * m by omega)
    have h14 : Nat.factorial 14 = 87178291200 := by decide
    omega

end CFSG.Holt.SL6
