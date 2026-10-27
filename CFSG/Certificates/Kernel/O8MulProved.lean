module

public import Certificates.Data.Kernel.O8.EnumK
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Pack
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Tactic.Polynomial.Basic

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.F4M CFSG.EvenSmallLie.OmegaEight.Stage2
  CFSG.EvenSmallLie.UnitarySix.YamadaPar

theorem sum_spread_lt (d : ℕ → ℕ) (hd : ∀ i, d i < 4096) : ∀ n,
    ∑ i ∈ Finset.range n, d i * 2 ^ (12 * i) < 2 ^ (12 * n)
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ]
    have h1 := sum_spread_lt d hd n
    have h2 : d n * 2 ^ (12 * n) ≤ 4095 * 2 ^ (12 * n) :=
      Nat.mul_le_mul_right _ (by have := hd n; omega)
    have e : 2 ^ (12 * (n + 1)) = 4096 * 2 ^ (12 * n) := by
      rw [Nat.mul_succ, pow_add]
      ring
    rw [e]
    omega

theorem testBit_spread (d : ℕ → ℕ) (hd : ∀ i, d i < 4096) (p : ℕ) : ∀ n,
    (∑ i ∈ Finset.range n, d i * 2 ^ (12 * i)).testBit p =
      (decide (p < 12 * n) && (d (p / 12)).testBit (p % 12))
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, add_comm, mul_comm (d n),
      Nat.testBit_two_pow_mul_add _ (sum_spread_lt d hd n)]
    by_cases h : p < 12 * n
    · simp only [h, ↓reduceIte]
      rw [testBit_spread d hd p n]
      simp [h, show p < 12 * (n + 1) by omega]
    · simp only [h, ↓reduceIte]
      by_cases h2 : p < 12 * (n + 1)
      · have e1 : p / 12 = n := by omega
        have e2 : p % 12 = p - 12 * n := by omega
        simp [h2, e1, e2]
      · have h3 : (d n).testBit (p - 12 * n) = false := by
          refine Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (hd n) ?_)
          calc (4096 : ℕ) = 2 ^ 12 := by norm_num
            _ ≤ 2 ^ (p - 12 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
        simp [h2, h3]

theorem testBit_toNat' (b : Bool) (m : ℕ) : b.toNat.testBit m = (b && decide (m = 0)) := by
  cases b
  · simp
  · cases m <;> simp [Nat.testBit_succ]

theorem low12_eq : low12 = ∑ i ∈ Finset.range 12, 1 * 2 ^ (12 * i) := by
  unfold low12
  simp [Finset.sum_range_succ]

theorem testBit_low12 (q : ℕ) : low12.testBit q = (decide (q < 144) && decide (q % 12 = 0)) := by
  rw [low12_eq, testBit_spread (fun _ => 1) (fun _ => by norm_num) q 12]
  have e : (1 : ℕ) = (true : Bool).toNat := rfl
  rw [e, testBit_toNat']
  simp

theorem sel_eq (a l : ℕ) : (a >>> l) &&& low12 =
    ∑ i ∈ Finset.range 12, (a.testBit (12 * i + l)).toNat * 2 ^ (12 * i) := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_low12,
    testBit_spread _ (fun i => by cases a.testBit (12 * i + l) <;> simp) q 12, testBit_toNat']
  by_cases h1 : q < 144
  · by_cases h2 : q % 12 = 0
    · have e : l + q = 12 * (q / 12) + l := by omega
      simp [h1, h2, e]
    · simp [h1, h2]
  · simp [h1]

theorem testBit_4095_mul (c : Bool) (r : ℕ) :
    (c.toNat * 4095).testBit r = (c && decide (r < 12)) := by
  cases c
  · simp
  · have e : (4095 : ℕ) = 2 ^ 12 - 1 := by norm_num
    rw [Bool.toNat_true, one_mul, e, Nat.testBit_two_pow_sub_one, Bool.true_and]

theorem testBit_selMul (a l p : ℕ) : (((a >>> l) &&& low12) * 4095).testBit p =
    (decide (p < 144) && a.testBit (12 * (p / 12) + l)) := by
  rw [sel_eq, Finset.sum_mul]
  have e : ∀ i ∈ Finset.range 12, (a.testBit (12 * i + l)).toNat * 2 ^ (12 * i) * 4095 =
      ((a.testBit (12 * i + l)).toNat * 4095) * 2 ^ (12 * i) := fun i _ => by ring
  rw [Finset.sum_congr rfl e, testBit_spread _ (fun i => by
    cases a.testBit (12 * i + l) <;> simp) p 12, testBit_4095_mul]
  have h : p % 12 < 12 := Nat.mod_lt _ (by norm_num)
  simp [h]

theorem maskN12 : maskN 12 = 2 ^ 12 - 1 := by decide

theorem row12_lt (b l : ℕ) : row12 b l < 4096 := by
  unfold row12 fget
  have e : maskN 12 = 4095 := by decide
  rw [e]
  exact Nat.lt_succ_of_le Nat.and_le_right

theorem testBit_row12 (b l r : ℕ) : (row12 b l).testBit r = (decide (r < 12) && b.testBit (12 * l + r)) := by
  unfold row12 fget
  change ((b >>> (l * 12)) &&& maskN 12).testBit r = _
  rw [maskN12, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, mul_comm l]
  cases decide (r < 12) <;> simp

theorem testBit_rowMul12 (b l p : ℕ) : (row12 b l * low12).testBit p =
    (decide (p < 144) && b.testBit (12 * l + p % 12)) := by
  rw [low12_eq, Finset.mul_sum]
  have e : ∀ i ∈ Finset.range 12, row12 b l * (1 * 2 ^ (12 * i)) = row12 b l * 2 ^ (12 * i) :=
    fun i _ => by ring
  rw [Finset.sum_congr rfl e, testBit_spread (fun _ => row12 b l) (fun _ => row12_lt b l) p 12,
    testBit_row12]
  have h : p % 12 < 12 := Nat.mod_lt _ (by norm_num)
  simp [h]

theorem strictN_eq_app (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by
  cases y <;> rfl

theorem testBit_xorN' (f : ℕ → ℕ) (p : ℕ) : ∀ n,
    (xorN n f).testBit p = xorFold n fun l => (f l).testBit p
  | 0 => by
    have e : xorN 0 f = 0 := rfl
    rw [e]
    simp [xorFold]
  | n + 1 => by
    have e : xorN (n + 1) f = f n ^^^ xorN n f := rfl
    rw [e, Nat.testBit_xor, xorFold_succ, testBit_xorN' f p n, Bool.xor_comm]

theorem xorFold_congr {k : ℕ} {f g : ℕ → Bool} (h : ∀ l < k, f l = g l) :
    xorFold k f = xorFold k g := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [xorFold_succ, xorFold_succ, ih (fun l hl => h l (by omega)), h k (by omega)]

theorem xorFold_false (k : ℕ) : xorFold k (fun _ => false) = false := by
  induction k with
  | zero => rfl
  | succ k ih => rw [xorFold_succ, ih]; rfl

theorem testBit_rowsOf (a i r : ℕ) (hi : i < 12) :
    ((rowsOf a).getD i 0).testBit r = (decide (r < 12) && a.testBit (12 * i + r)) := by
  have e : (rowsOf a).getD i 0 = (a >>> (12 * i)) % 2 ^ 12 := by
    simp [rowsOf, Array.getD_eq_getD_getElem?, hi]
  rw [e, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

public theorem mulK_eq_proved (a b : ℕ) : mulK a b = mul12K a b := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [mulK, testBit_keyOf]
  unfold mul12K
  rw [strictN_eq_app, strictN_eq_app]
  change _ = (xorN 12 fun l => ((a >>> l) &&& low12) * 4095 &&& row12 b l * low12).testBit p
  rw [testBit_xorN']
  simp only [Nat.testBit_and, testBit_selMul, testBit_rowMul12]
  by_cases hp : p < 144
  · have hq : p / 12 < 12 := by omega
    have e : (bmul 12 12 (rowsOf a) (rowsOf b)).getD (p / 12) 0 =
        rowMul 12 ((rowsOf a).getD (p / 12) 0) (rowsOf b) := by
      simp [bmul, Array.getD_eq_getD_getElem?, hq]
    rw [e, testBit_rowMul]
    simp only [hp, decide_true, Bool.true_and]
    apply xorFold_congr
    intro l hl
    rw [testBit_rowsOf a _ l hq, testBit_rowsOf b l _ hl]
    have h2 : p % 12 < 12 := Nat.mod_lt _ (by norm_num)
    simp [hl, h2]
  · simp only [hp, decide_false, Bool.false_and, Bool.and_false]
    exact (xorFold_false 12).symm

end CFSG.KC.O8
