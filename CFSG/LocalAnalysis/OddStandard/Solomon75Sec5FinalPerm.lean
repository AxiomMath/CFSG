module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5DefsModel

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm

section Pts

variable {n : ℕ}

@[expose] def pt (hn : 8 ≤ n) (i : Fin 8) : Fin n := Fin.castLE hn i

theorem pt_injective (hn : 8 ≤ n) : Function.Injective (pt hn) := Fin.castLE_injective hn

theorem pt_ne (hn : 8 ≤ n) {i j : Fin 8} (h : i ≠ j) : pt hn i ≠ pt hn j :=
  fun h' => h (pt_injective hn h')

@[expose] def oddOne (hn : 8 ≤ n) : Perm (Fin n) := swap (pt hn 0) (pt hn 1)

@[expose] def dblTwo (hn : 8 ≤ n) : Perm (Fin n) :=
  swap (pt hn 2) (pt hn 3) * swap (pt hn 4) (pt hn 5)

theorem oddOne_sq (hn : 8 ≤ n) : oddOne hn * oddOne hn = 1 := swap_mul_self _ _

theorem dblTwo_sq (hn : 8 ≤ n) : dblTwo hn * dblTwo hn = 1 :=
  dbl_mul_self (pt_ne hn (by decide)) (pt_ne hn (by decide)) (pt_ne hn (by decide))
    (pt_ne hn (by decide)) (pt_ne hn (by decide)) (pt_ne hn (by decide))

theorem card_support_dblTwo (hn : 8 ≤ n) : (dblTwo hn).support.card = 4 :=
  card_support_dbl (pt_ne hn (by decide)) (pt_ne hn (by decide)) (pt_ne hn (by decide))
    (pt_ne hn (by decide)) (pt_ne hn (by decide)) (pt_ne hn (by decide))

theorem card_support_oddOne (hn : 8 ≤ n) : (oddOne hn).support.card = 2 :=
  card_support_swap (pt_ne hn (by decide))

theorem dblTwo_isDblI (hn : 8 ≤ n) : AhatData.DblI (dblTwo hn) :=
  ⟨dblTwo_sq hn, card_support_dblTwo hn⟩

theorem sign_oddOne (hn : 8 ≤ n) : sign (oddOne hn) = -1 :=
  sign_swap (pt_ne hn (by decide))

theorem sign_dblTwo (hn : 8 ≤ n) : sign (dblTwo hn) = 1 := by
  unfold dblTwo
  rw [Perm.sign_mul, sign_swap (pt_ne hn (by decide)), sign_swap (pt_ne hn (by decide))]
  decide

theorem oddOne_apply_of_ne (hn : 8 ≤ n) {i : Fin 8} (h0 : i ≠ 0) (h1 : i ≠ 1) :
    oddOne hn (pt hn i) = pt hn i :=
  swap_apply_of_ne_of_ne (pt_ne hn h0) (pt_ne hn h1)

theorem dblTwo_apply_zero (hn : 8 ≤ n) : dblTwo hn (pt hn 0) = pt hn 0 := by
  unfold dblTwo
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne (pt_ne hn (by decide)) (pt_ne hn (by decide)),
    swap_apply_of_ne_of_ne (pt_ne hn (by decide)) (pt_ne hn (by decide))]

theorem dblTwo_apply_one (hn : 8 ≤ n) : dblTwo hn (pt hn 1) = pt hn 1 := by
  unfold dblTwo
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne (pt_ne hn (by decide)) (pt_ne hn (by decide)),
    swap_apply_of_ne_of_ne (pt_ne hn (by decide)) (pt_ne hn (by decide))]

theorem disjoint_oddOne_dblTwo (hn : 8 ≤ n) : (oddOne hn).Disjoint (dblTwo hn) := by
  intro x
  by_cases hx : x = pt hn 0 ∨ x = pt hn 1
  · right
    rcases hx with rfl | rfl
    · exact dblTwo_apply_zero hn
    · exact dblTwo_apply_one hn
  · left
    push Not at hx
    exact swap_apply_of_ne_of_ne hx.1 hx.2

theorem oddOne_dblTwo_comm (hn : 8 ≤ n) : oddOne hn * dblTwo hn = dblTwo hn * oddOne hn :=
  (disjoint_oddOne_dblTwo hn).commute.eq

theorem card_support_oddOne_mul_dblTwo (hn : 8 ≤ n) :
    (oddOne hn * dblTwo hn).support.card = 6 := by
  rw [(disjoint_oddOne_dblTwo hn).card_support_mul, card_support_oddOne, card_support_dblTwo]

theorem sign_oddOne_mul_dblTwo (hn : 8 ≤ n) : sign (oddOne hn * dblTwo hn) = -1 := by
  rw [Perm.sign_mul, sign_oddOne, sign_dblTwo, mul_one]

theorem oddOne_mul_dblTwo_sq (hn : 8 ≤ n) :
    (oddOne hn * dblTwo hn) * (oddOne hn * dblTwo hn) = 1 := by
  calc (oddOne hn * dblTwo hn) * (oddOne hn * dblTwo hn)
      = oddOne hn * (dblTwo hn * oddOne hn) * dblTwo hn := by group
    _ = oddOne hn * (oddOne hn * dblTwo hn) * dblTwo hn := by rw [oddOne_dblTwo_comm hn]
    _ = (oddOne hn * oddOne hn) * (dblTwo hn * dblTwo hn) := by group
    _ = 1 := by rw [oddOne_sq, dblTwo_sq, one_mul]

theorem fixCount_oddOne (hn : 8 ≤ n) : 6 ≤ fixCount (oddOne hn) := by
  have h := fixCount_add_support (oddOne hn)
  rw [card_support_oddOne] at h
  omega

theorem transCount_oddOne_mul_dblTwo (hn : 8 ≤ n) : transCount (oddOne hn * dblTwo hn) = 3 := by
  unfold transCount
  rw [card_support_oddOne_mul_dblTwo]

end Pts

end CFSG.OddStandard.Solomon75
