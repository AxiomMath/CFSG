module

public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Zify
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.SeitzReduction.F4Pilot

inductive Sp6Kind
  | field
  | swap
  | linear6
  | unitary6
  | linear7
  | unitary7
  | omegaPlus8
  | omegaMinus8
  deriving DecidableEq

@[expose] def ordSL (n q : ℕ) : ℕ :=
  q ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 2 n, (q ^ j - 1)

@[expose] def ordSU (n q : ℕ) : ℕ :=
  q ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 2 n, (if j % 2 = 0 then q ^ j - 1 else q ^ j + 1)

@[expose] def ordSp (r q : ℕ) : ℕ :=
  q ^ (r ^ 2) * ∏ j ∈ Finset.Icc 1 r, (q ^ (2 * j) - 1)

@[expose] def pieceOrders : Sp6Kind → ℕ → ℕ × ℕ × ℕ
  | .field, q => (ordSp 2 (q ^ 2), ordSL 2 (q ^ 2), ordSL 2 (q ^ 2))
  | .swap, q => (ordSp 2 q ^ 2, ordSL 2 q ^ 2, ordSL 2 q ^ 2)
  | .linear6, q => (ordSL 4 q, ordSL 2 q, ordSL 2 q ^ 2)
  | .unitary6, q => (ordSU 4 q, ordSL 2 q, ordSL 2 (q ^ 2))
  | .linear7, q => (ordSL 5 q, ordSL 3 q, ordSL 2 q ^ 2)
  | .unitary7, q => (ordSU 5 q, ordSU 3 q, ordSL 2 (q ^ 2))
  | .omegaPlus8, q => (ordSL 4 q, ordSL 2 q ^ 2, ordSL 2 q)
  | .omegaMinus8, q => (ordSU 4 q, ordSL 2 (q ^ 2), ordSL 2 q)

@[expose] def swapPieces (x : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (x.1, x.2.2, x.2.1)

@[simp] theorem swapPieces_swapPieces (x : ℕ × ℕ × ℕ) : swapPieces (swapPieces x) = x := rfl

@[expose] def consistentKindPairs : List (Sp6Kind × Sp6Kind) :=
  [(.field, .field), (.swap, .swap), (.linear6, .omegaPlus8), (.omegaPlus8, .linear6),
    (.unitary6, .omegaMinus8), (.omegaMinus8, .unitary6)]

theorem ordSL_two (q : ℕ) : ordSL 2 q = q * (q ^ 2 - 1) := by
  simp [ordSL]

theorem ordSL_three (q : ℕ) : ordSL 3 q = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  rw [ordSL, Finset.prod_Icc_succ_top (by norm_num), Finset.Icc_self, Finset.prod_singleton]

theorem ordSL_four (q : ℕ) :
    ordSL 4 q = q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1)) := by
  rw [ordSL, Finset.prod_Icc_succ_top (by norm_num), Finset.prod_Icc_succ_top (by norm_num),
    Finset.Icc_self, Finset.prod_singleton]

theorem ordSL_five (q : ℕ) :
    ordSL 5 q = q ^ 10 * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) * (q ^ 5 - 1)) := by
  rw [ordSL, Finset.prod_Icc_succ_top (by norm_num), Finset.prod_Icc_succ_top (by norm_num),
    Finset.prod_Icc_succ_top (by norm_num), Finset.Icc_self, Finset.prod_singleton]

theorem ordSU_three (q : ℕ) : ordSU 3 q = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  rw [ordSU, Finset.prod_Icc_succ_top (by norm_num), Finset.Icc_self, Finset.prod_singleton]
  norm_num

theorem ordSU_four (q : ℕ) :
    ordSU 4 q = q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1)) := by
  rw [ordSU, Finset.prod_Icc_succ_top (by norm_num), Finset.prod_Icc_succ_top (by norm_num),
    Finset.Icc_self, Finset.prod_singleton]
  norm_num

theorem ordSU_five (q : ℕ) :
    ordSU 5 q = q ^ 10 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) * (q ^ 5 + 1)) := by
  rw [ordSU, Finset.prod_Icc_succ_top (by norm_num), Finset.prod_Icc_succ_top (by norm_num),
    Finset.prod_Icc_succ_top (by norm_num), Finset.Icc_self, Finset.prod_singleton]
  norm_num

theorem ordSp_two (q : ℕ) : ordSp 2 q = q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
  rw [ordSp, Finset.prod_Icc_succ_top (by norm_num), Finset.Icc_self, Finset.prod_singleton]
  norm_num

private theorem cast_pow_sub_one {q : ℕ} (hq : 1 ≤ q) (j : ℕ) :
    ((q ^ j - 1 : ℕ) : ℤ) = (q : ℤ) ^ j - 1 := by
  rw [Nat.cast_sub (Nat.one_le_pow _ _ hq)]
  push_cast
  ring

private theorem cast_add_two_pow_sub_one (p j : ℕ) :
    (((p + 2) ^ j - 1 : ℕ) : ℤ) = ((p : ℤ) + 2) ^ j - 1 := by
  rw [cast_pow_sub_one (by omega)]
  push_cast
  ring

private theorem pow_two_pow (q j : ℕ) : (q ^ 2) ^ j = q ^ (2 * j) := (pow_mul q 2 j).symm

theorem ordSL_four_lt_ordSU_four {q : ℕ} (hq : 2 ≤ q) : ordSL 4 q < ordSU 4 q := by
  rw [ordSL_four, ordSU_four]
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 2 := ⟨q - 2, by omega⟩
  zify
  simp only [cast_add_two_pow_sub_one]
  rw [← sub_pos]
  ring_nf
  positivity

theorem ordSU_four_lt_ordSp_two_sq {q : ℕ} (hq : 2 ≤ q) : ordSU 4 q < ordSp 2 q ^ 2 := by
  rw [ordSU_four, ordSp_two]
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 2 := ⟨q - 2, by omega⟩
  zify
  simp only [cast_add_two_pow_sub_one]
  rw [← sub_pos]
  ring_nf
  positivity

theorem ordSp_two_sq_lt_ordSp_two_sq' {q : ℕ} (hq : 2 ≤ q) : ordSp 2 q ^ 2 < ordSp 2 (q ^ 2) := by
  rw [ordSp_two, ordSp_two]
  simp only [pow_two_pow]
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 2 := ⟨q - 2, by omega⟩
  zify
  simp only [cast_add_two_pow_sub_one]
  rw [← sub_pos]
  ring_nf
  positivity

theorem ordSp_two_sq'_lt_ordSL_five {q : ℕ} (hq : 2 ≤ q) : ordSp 2 (q ^ 2) < ordSL 5 q := by
  rw [ordSp_two, ordSL_five]
  simp only [pow_two_pow]
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 2 := ⟨q - 2, by omega⟩
  zify
  simp only [cast_add_two_pow_sub_one]
  rw [← sub_pos]
  ring_nf
  positivity

theorem ordSL_five_lt_ordSU_five {q : ℕ} (hq : 2 ≤ q) : ordSL 5 q < ordSU 5 q := by
  rw [ordSL_five, ordSU_five]
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 2 := ⟨q - 2, by omega⟩
  zify
  simp only [cast_add_two_pow_sub_one]
  rw [← sub_pos]
  ring_nf
  positivity

theorem ordSL_two_lt_sq {q : ℕ} (hq : 2 ≤ q) : ordSL 2 q < ordSL 2 q ^ 2 := by
  rw [ordSL_two]
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 2 := ⟨q - 2, by omega⟩
  zify
  simp only [cast_add_two_pow_sub_one]
  rw [← sub_pos]
  ring_nf
  positivity

theorem ordSL_two_lt_ordSL_two_sq {q : ℕ} (hq : 2 ≤ q) : ordSL 2 q < ordSL 2 (q ^ 2) := by
  rw [ordSL_two, ordSL_two]
  simp only [pow_two_pow]
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 2 := ⟨q - 2, by omega⟩
  zify
  simp only [cast_add_two_pow_sub_one]
  rw [← sub_pos]
  ring_nf
  positivity

theorem ordSL_two_sq_lt_ordSL_three {q : ℕ} (hq : 2 ≤ q) : ordSL 2 q ^ 2 < ordSL 3 q := by
  rw [ordSL_two, ordSL_three]
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 2 := ⟨q - 2, by omega⟩
  zify
  simp only [cast_add_two_pow_sub_one]
  rw [← sub_pos]
  ring_nf
  positivity

theorem ordSL_two_sq'_lt_ordSU_three {q : ℕ} (hq : 2 ≤ q) : ordSL 2 (q ^ 2) < ordSU 3 q := by
  rw [ordSL_two, ordSU_three]
  simp only [pow_two_pow]
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 2 := ⟨q - 2, by omega⟩
  zify
  simp only [cast_add_two_pow_sub_one]
  rw [← sub_pos]
  ring_nf
  positivity

theorem pieceOrders_swap_eq_iff {q : ℕ} (hq : 2 ≤ q) (κ κ' : Sp6Kind) :
    pieceOrders κ q = swapPieces (pieceOrders κ' q) ↔ (κ, κ') ∈ consistentKindPairs := by
  have c1 := ordSL_four_lt_ordSU_four hq
  have c2 := ordSU_four_lt_ordSp_two_sq hq
  have c3 := ordSp_two_sq_lt_ordSp_two_sq' hq
  have c4 := ordSp_two_sq'_lt_ordSL_five hq
  have c5 := ordSL_five_lt_ordSU_five hq
  have m1 := ordSL_two_lt_sq hq
  have m2 := ordSL_two_lt_ordSL_two_sq hq
  have m3 := ordSL_two_sq_lt_ordSL_three hq
  have m4 := ordSL_two_sq'_lt_ordSU_three hq
  cases κ <;> cases κ' <;>
    simp [pieceOrders, swapPieces, consistentKindPairs, Prod.ext_iff] <;> omega

theorem mem_consistentKindPairs_of_pieceOrders {q : ℕ} (hq : 2 ≤ q) {κX κY : Sp6Kind}
    {t : ℕ × ℕ × ℕ} (hX : t = pieceOrders κX q) (hY : swapPieces t = pieceOrders κY q) :
    (κX, κY) ∈ consistentKindPairs := by
  rw [← pieceOrders_swap_eq_iff hq, ← hX, ← hY, swapPieces_swapPieces]

theorem kinds_ne_linear7_unitary7_of_pieceOrders {q : ℕ} (hq : 2 ≤ q) {κX κY : Sp6Kind}
    {t : ℕ × ℕ × ℕ} (hX : t = pieceOrders κX q) (hY : swapPieces t = pieceOrders κY q) :
    κX ≠ .linear7 ∧ κX ≠ .unitary7 ∧ κY ≠ .linear7 ∧ κY ≠ .unitary7 := by
  have h := mem_consistentKindPairs_of_pieceOrders hq hX hY
  revert h
  cases κX <;> cases κY <;> simp [consistentKindPairs]

end CFSG.SeitzReduction.F4Pilot
