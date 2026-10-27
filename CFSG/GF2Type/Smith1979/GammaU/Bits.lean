module

public import CFSG.GF2Type.Smith1979.GammaU.Model
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.GF2Type.Smith1979.GammaU

@[expose] def vecOf (n : ℕ) : V12 := fun j => if n.testBit j then 1 else 0

@[expose] def codeOf (x : V12) : ℕ :=
  (x 0).val + 2 * (x 1).val + 4 * (x 2).val + 8 * (x 3).val + 16 * (x 4).val + 32 * (x 5).val +
    64 * (x 6).val + 128 * (x 7).val + 256 * (x 8).val + 512 * (x 9).val +
    1024 * (x 10).val + 2048 * (x 11).val

theorem zmod2_val_le_one (a : ZMod 2) : a.val ≤ 1 := by
  have := ZMod.val_lt a
  omega

theorem codeOf_lt (x : V12) : codeOf x < 4096 := by
  have h := fun j => zmod2_val_le_one (x j)
  have := h 0; have := h 1; have := h 2; have := h 3; have := h 4; have := h 5
  have := h 6; have := h 7; have := h 8; have := h 9; have := h 10; have := h 11
  unfold codeOf
  omega

theorem testBit_codeOf (x : V12) (j : Fin 12) : (codeOf x).testBit j = decide ((x j).val = 1) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  congr 1
  have h := fun j => zmod2_val_le_one (x j)
  have := h 0; have := h 1; have := h 2; have := h 3; have := h 4; have := h 5
  have := h 6; have := h 7; have := h 8; have := h 9; have := h 10; have := h 11
  unfold codeOf
  apply propext
  fin_cases j <;> simp <;> omega

theorem vecOf_codeOf (x : V12) : vecOf (codeOf x) = x := by
  funext j
  rw [vecOf, testBit_codeOf]
  generalize x j = a
  revert a
  decide

theorem forall_of_forall_code {P : V12 → Prop} (h : ∀ n < 4096, P (vecOf n)) (x : V12) : P x := by
  rw [← vecOf_codeOf x]
  exact h _ (codeOf_lt x)

theorem ite_add_ite (p q : Bool) :
    ((if p then 1 else 0 : ZMod 2) + if q then 1 else 0) = if (p ^^ q) then 1 else 0 := by
  cases p <;> cases q <;> decide

theorem vecOf_xor (a b : ℕ) : vecOf (a ^^^ b) = vecOf a + vecOf b := by
  funext j
  simp only [vecOf, Nat.testBit_xor, Pi.add_apply, ite_add_ite]

@[simp] theorem vecOf_zero : vecOf 0 = 0 := by
  funext j
  simp [vecOf]

@[expose] def q0b (n : ℕ) : Bool :=
  (List.range 6).foldl (fun acc i => acc ^^ (n.testBit i || n.testBit (i + 6))) false

theorem norm_term (p q : Bool) :
    ((if p then 1 else 0 : ZMod 2) + (if p then 1 else 0) * (if q then 1 else 0) +
      if q then 1 else 0) = if (p || q) then 1 else 0 := by
  cases p <;> cases q <;> decide

theorem q0_vecOf (n : ℕ) : q0 (vecOf n) = if q0b n then 1 else 0 := by
  simp only [q0, vecOf, Fin.sum_univ_six, q0b, List.range_succ, List.range_zero, List.nil_append,
    List.foldl_append, List.foldl_cons, List.foldl_nil, Bool.false_xor, norm_term, ite_add_ite]
  rfl

@[expose] def theta0N (n : ℕ) : ℕ := (n >>> 6) ||| (((n &&& 63) ^^^ (n >>> 6)) <<< 6)

theorem testBit_of_lt {n : ℕ} (hn : n < 4096) {k : ℕ} (hk : 12 ≤ k) : n.testBit k = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hn (by
    calc 4096 = 2 ^ 12 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk))

theorem testBit_theta0N_lo (n : ℕ) {i : ℕ} (hi : i < 6) :
    (theta0N n).testBit i = n.testBit (6 + i) := by
  have h : ¬ (6 ≤ i) := by omega
  simp [theta0N, Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft, h]

theorem testBit_theta0N_hi {n : ℕ} (hn : n < 4096) {i : ℕ} (hi : i < 6) :
    (theta0N n).testBit (6 + i) = (n.testBit i ^^ n.testBit (6 + i)) := by
  have h12 : n.testBit (6 + (6 + i)) = false := testBit_of_lt hn (by omega)
  have h63 : (63 : ℕ).testBit i = true := by
    rw [show (63 : ℕ) = 2 ^ 6 - 1 by norm_num, Nat.testBit_two_pow_sub_one, decide_eq_true_iff]
    exact hi
  have hsub : 6 + i - 6 = i := by omega
  simp only [theta0N, Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft,
    Nat.testBit_xor, Nat.testBit_and, h12, h63, hsub, Bool.and_true, Bool.false_or]
  simp

theorem vecOf_theta0N {n : ℕ} (hn : n < 4096) : vecOf (theta0N n) = theta0 (vecOf n) := by
  refine ext_lo_hi (fun i => ?_) (fun i => ?_)
  · rw [theta0_lo]
    simp only [vecOf, lo, hi, Fin.coe_castAdd, Fin.coe_natAdd, testBit_theta0N_lo n i.isLt]
  · rw [theta0_hi]
    simp only [vecOf, lo, hi, Fin.coe_castAdd, Fin.coe_natAdd, testBit_theta0N_hi hn i.isLt,
      ite_add_ite]

@[expose] def linOfRows (rows : Array ℕ) : V12 →ₗ[ZMod 2] V12 where
  toFun x := ∑ j : Fin 12, x j • vecOf rows[(j : ℕ)]!
  map_add' x y := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, Finset.smul_sum]

theorem linOfRows_apply (rows : Array ℕ) (x : V12) :
    linOfRows rows x = ∑ j : Fin 12, x j • vecOf rows[(j : ℕ)]! := rfl

@[expose] def appN (rows : Array ℕ) (n : ℕ) : ℕ :=
  (List.range 12).foldl (fun acc j => if n.testBit j then acc ^^^ rows[j]! else acc) 0

theorem foldl_appN (rows : Array ℕ) (n : ℕ) (k : ℕ) :
    vecOf ((List.range k).foldl (fun acc j => if n.testBit j then acc ^^^ rows[j]! else acc) 0) =
      ∑ j ∈ Finset.range k, (if n.testBit j then (1 : ZMod 2) else 0) • vecOf rows[j]! := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Finset.sum_range_succ, ← ih]
    split_ifs with h
    · rw [vecOf_xor, one_smul]
    · rw [zero_smul, add_zero]

theorem vecOf_appN (rows : Array ℕ) (n : ℕ) : vecOf (appN rows n) = linOfRows rows (vecOf n) := by
  rw [appN, foldl_appN, linOfRows_apply, Finset.sum_range (fun j =>
    (if n.testBit j then (1 : ZMod 2) else 0) • vecOf rows[j]!)]
  rfl

end CFSG.GF2Type.Smith1979.GammaU
