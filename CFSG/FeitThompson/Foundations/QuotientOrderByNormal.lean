module

import Mathlib.Algebra.Order.Ring.Abs
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {G : Type*} [Group G] (N : Subgroup G)

theorem natCard_quotient_eq_natCard_div [Finite G] :
    Nat.card (G ⧸ N) = Nat.card G / Nat.card N := by
  have h : Nat.card G = Nat.card (G ⧸ N) * Nat.card N := by
    rw [← Subgroup.index_eq_card, ← natCard_range_leftCoset N,
      ← natCard_eq_natCard_range_leftCoset_mul_natCard N]
  rw [h, Nat.mul_div_cancel _ Nat.card_pos]

theorem natCard_quotient_lt_natCard_of_bot_lt [Finite G] (h : ⊥ < N) :
    Nat.card (G ⧸ N) < Nat.card G :=
  calc Nat.card (G ⧸ N) < Nat.card (G ⧸ N) * Nat.card N :=
        (lt_mul_iff_one_lt_right Nat.card_pos).2 ((Subgroup.one_lt_card_iff_ne_bot N).2 h.ne')
    _ = Nat.card G := (Subgroup.card_eq_card_quotient_mul_card_subgroup N).symm

theorem two_le_natCard_of_bot_lt [Finite N] (h : ⊥ < N) : 2 ≤ Nat.card N :=
  (Subgroup.one_lt_card_iff_ne_bot N).2 h.ne'

theorem two_le_natCard_quotient_of_lt_top [Finite (G ⧸ N)] (h : N < ⊤) :
    2 ≤ Nat.card (G ⧸ N) := by
  rw [← Subgroup.index_eq_card]
  exact Subgroup.one_lt_index_of_ne_top h.ne

theorem odd_natCard_quotient (h : Odd (Nat.card G)) : Odd (Nat.card (G ⧸ N)) :=
  h.of_dvd_nat N.card_quotient_dvd_card

end

end CFSG.FeitThompson
