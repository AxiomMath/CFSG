module

public import Certificates.Data.Kernel.J4Q.Pack
public import CFSG.Sporadic.J4.QTRankNative
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KC.J4Q

open CFSG.Sporadic.J4.QT

private theorem nrec_succ {α : Type} (z : α) (f : Nat → α → α) (n : Nat) :
    Nat.rec (motive := fun _ => α) z f (n + 1) = f n (Nat.rec (motive := fun _ => α) z f n) := rfl

private theorem recX_congr {f g : Nat → Nat} : ∀ n, (∀ k < n, f k = g k) →
    Nat.rec (motive := fun _ => Nat) 0 (fun k acc => acc ^^^ f k) n =
      Nat.rec (motive := fun _ => Nat) 0 (fun k acc => acc ^^^ g k) n
  | 0, _ => rfl
  | n + 1, h =>
    congrArg₂ (· ^^^ ·) (recX_congr n fun k hk => h k (by omega)) (h n (by omega))

private theorem recX_lt {f : Nat → Nat} {w : Nat} : ∀ n, (∀ k < n, f k < 2 ^ w) →
    Nat.rec (motive := fun _ => Nat) 0 (fun k acc => acc ^^^ f k) n < 2 ^ w
  | 0, _ => Nat.two_pow_pos w
  | n + 1, h => Nat.xor_lt_two_pow (recX_lt n fun k hk => h k (by omega)) (h n (by omega))

private theorem testBit_recX (g : Nat → Nat) (i : Nat) : ∀ n,
    (Nat.rec (motive := fun _ => Nat) 0 (fun k acc => acc ^^^ g k) n).testBit i =
      Nat.rec (motive := fun _ => Bool) false (fun k acc => acc ^^ (g k).testBit i) n
  | 0 => Nat.zero_testBit i
  | n + 1 => (Nat.testBit_xor _ _ _).trans (congrArg (· ^^ (g n).testBit i) (testBit_recX g i n))

private theorem recB_congr {f g : Nat → Bool} : ∀ n, (∀ k < n, f k = g k) →
    Nat.rec (motive := fun _ => Bool) false (fun k acc => acc ^^ f k) n =
      Nat.rec (motive := fun _ => Bool) false (fun k acc => acc ^^ g k) n
  | 0, _ => rfl
  | n + 1, h =>
    congrArg₂ (· ^^ ·) (recB_congr n fun k hk => h k (by omega)) (h n (by omega))

private theorem recB_false : ∀ n,
    Nat.rec (motive := fun _ => Bool) false (fun _ acc => acc ^^ false) n = false
  | 0 => rfl
  | n + 1 => (congrArg (· ^^ false) (recB_false n)).trans (Bool.xor_false false)

private theorem foldl_range_rec {α : Type} (F : α → Nat → α) (a : α) : ∀ n,
    (List.range n).foldl F a = Nat.rec (motive := fun _ => α) a (fun k acc => F acc k) n
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, foldl_range_rec F a n]
    rfl

private theorem rowsXor_rec (r : Nat → Nat) (m c : Nat) :
    rowsXor r m c = Nat.rec (motive := fun _ => Nat) 0
      (fun k acc => acc ^^^ if c.testBit k then r k else 0) m := by
  unfold rowsXor
  rw [foldl_range_rec]
  congr
  funext k acc
  split <;> simp

private theorem shr_and_one (c k : Nat) : (c >>> k) &&& 1 = if c.testBit k then 1 else 0 := by
  rw [Nat.and_one_is_mod]
  have ht : c.testBit k = decide ((c >>> k) % 2 = 1) := by
    rw [← Nat.testBit_zero, Nat.testBit_shiftRight, Nat.add_zero]
  rcases Nat.mod_two_eq_zero_or_one (c >>> k) with h | h <;> simp [ht, h]

private theorem fldP_eq (p j : Nat) : fldP p j = (p >>> (11 * j)) &&& 2047 := rfl

private theorem fldP_lt (p j : Nat) : fldP p j < 2 ^ 11 :=
  Nat.and_lt_two_pow _ (by norm_num)

private theorem testBit_2047 (i : Nat) : (2047 : Nat).testBit i = decide (i < 11) := by
  rw [show (2047 : Nat) = 2 ^ 11 - 1 by norm_num, Nat.testBit_two_pow_sub_one]

private theorem getD_unpackP (p : Nat) {j : Nat} (hj : j < 11) : (unpackP p).getD j 0 = fldP p j := by
  simp [unpackP, List.getD_eq_getElem?_getD, hj, fldP_eq]

private theorem testBit_fldP (p j i : Nat) :
    (fldP p j).testBit i = (decide (i < 11) && p.testBit (11 * j + i)) := by
  rw [fldP_eq, Nat.testBit_and, Nat.testBit_shiftRight, testBit_2047, Bool.and_comm]

private def spr (b : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun j acc => acc + b j * 2 ^ (11 * j)) n

private theorem spr_succ (b : Nat → Nat) (n : Nat) : spr b (n + 1) = spr b n + b n * 2 ^ (11 * n) := rfl

private theorem spr_lt {b : Nat → Nat} (hb : ∀ j, b j < 2 ^ 11) : ∀ n, spr b n < 2 ^ (11 * n)
  | 0 => by simp [spr]
  | n + 1 => by
    rw [spr_succ]
    have ih := spr_lt hb n
    have h1 : b n + 1 ≤ 2 ^ 11 := hb n
    calc spr b n + b n * 2 ^ (11 * n) < 2 ^ (11 * n) + b n * 2 ^ (11 * n) :=
          Nat.add_lt_add_right ih _
      _ = (b n + 1) * 2 ^ (11 * n) := by ring
      _ ≤ 2 ^ 11 * 2 ^ (11 * n) := Nat.mul_le_mul_right _ h1
      _ = 2 ^ (11 * (n + 1)) := by rw [← Nat.pow_add]; ring_nf

private theorem testBit_spr {b : Nat → Nat} (hb : ∀ j, b j < 2 ^ 11) : ∀ n m,
    (spr b n).testBit m = (decide (m < 11 * n) && (b (m / 11)).testBit (m % 11))
  | 0, m => by simp [spr]
  | n + 1, m => by
    rw [spr_succ, Nat.add_comm, ← Nat.shiftLeft_eq,
      Nat.shiftLeft_add_eq_or_of_lt (spr_lt hb n), Nat.testBit_or, Nat.testBit_shiftLeft,
      testBit_spr hb n m]
    by_cases h1 : m < 11 * n
    · simp [h1, show m < 11 * (n + 1) by omega, show ¬ 11 * n ≤ m by omega]
    · by_cases h2 : m < 11 * (n + 1)
      · have hq : m / 11 = n := by omega
        have hr : m % 11 = m - 11 * n := by omega
        simp [h1, h2, show 11 * n ≤ m by omega, hq, hr]
      · have hz : (b n).testBit (m - 11 * n) = false :=
          Nat.testBit_lt_two_pow ((hb n).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))
        simp [h1, h2, hz]

private theorem spr_congr {b c : Nat → Nat} : ∀ n, (∀ j < n, b j = c j) → spr b n = spr c n
  | 0, _ => rfl
  | n + 1, h => by rw [spr_succ, spr_succ, spr_congr n fun j hj => h j (by omega), h n (by omega)]

private theorem mul_spr (a : Nat) (b : Nat → Nat) : ∀ n, spr b n * a = spr (fun j => b j * a) n
  | 0 => by simp [spr]
  | n + 1 => by rw [spr_succ, spr_succ, Nat.add_mul, mul_spr a b n]; ring

private theorem ONES_eq : ONES = spr (fun _ => 1) 11 := by
  unfold ONES spr
  rfl

private theorem spr_one_mul (a : Nat) : a * ONES = spr (fun _ => a) 11 := by
  rw [ONES_eq, Nat.mul_comm, mul_spr]
  simp

private theorem testBit_ite_one (b : Bool) (i : Nat) :
    (if b = true then 1 else 0 : Nat).testBit i = (b && decide (i = 0)) := by
  cases b
  · simp
  · simp only [↓reduceIte]
    rw [← Nat.pow_zero 2, Nat.testBit_two_pow]
    simp [eq_comm]

private theorem shr_and_ONES (q k : Nat) :
    (q >>> k) &&& ONES = spr (fun j => if q.testBit (11 * j + k) then 1 else 0) 11 := by
  have hb : ∀ j, (if q.testBit (11 * j + k) then 1 else 0 : Nat) < 2 ^ 11 := by
    intro j
    split <;> norm_num
  apply Nat.eq_of_testBit_eq
  intro m
  rw [Nat.testBit_and, Nat.testBit_shiftRight, ONES_eq, testBit_spr (fun _ => by norm_num),
    testBit_spr hb, testBit_ite_one]
  have h1 : (1 : Nat).testBit (m % 11) = decide (m % 11 = 0) := by
    rw [← Nat.pow_zero 2, Nat.testBit_two_pow]
    simp [eq_comm]
  rw [h1]
  by_cases hm : m % 11 = 0
  · have hmm : 11 * (m / 11) + k = k + m := by omega
    rw [hmm]
    simp [hm, Bool.and_comm]
  · simp [hm]

private theorem compB_term (p q k : Nat) :
    (((q >>> k) &&& ONES) * 2047) &&& (fldP p k * ONES) =
      spr (fun j => if q.testBit (11 * j + k) then fldP p k else 0) 11 := by
  have hb : ∀ j, (if q.testBit (11 * j + k) then fldP p k else 0) < 2 ^ 11 := by
    intro j
    split
    · exact fldP_lt p k
    · norm_num
  have hb2 : ∀ j, (if q.testBit (11 * j + k) then 1 else 0 : Nat) * 2047 < 2 ^ 11 := by
    intro j
    split <;> norm_num
  apply Nat.eq_of_testBit_eq
  intro m
  rw [Nat.testBit_and, shr_and_ONES, mul_spr, spr_one_mul, testBit_spr hb2,
    testBit_spr (fun _ => fldP_lt p k), testBit_spr hb]
  have hr : m % 11 < 11 := Nat.mod_lt _ (by norm_num)
  by_cases hm : m < 11 * 11
  · by_cases hq : q.testBit (11 * (m / 11) + k) = true
    · simp [hm, hq, testBit_2047, hr]
    · simp [hm, hq]
  · simp [hm]

private theorem testBit_rec_spr (B : Nat → Nat → Nat) (hB : ∀ k j, B k j < 2 ^ 11) (n m : Nat) :
    (Nat.rec (motive := fun _ => Nat) 0 (fun k acc => acc ^^^ spr (B k) 11) n).testBit m =
      (spr (fun j => Nat.rec (motive := fun _ => Nat) 0 (fun k acc => acc ^^^ B k j) n) 11).testBit m := by
  have hX : ∀ j, Nat.rec (motive := fun _ => Nat) 0 (fun k acc => acc ^^^ B k j) n < 2 ^ 11 :=
    fun j => recX_lt n fun k _ => hB k j
  rw [testBit_recX, testBit_spr hX, testBit_recX]
  by_cases hm : m < 11 * 11
  · rw [decide_eq_true hm, Bool.true_and]
    exact recB_congr n fun k _ => by rw [testBit_spr (hB k), decide_eq_true hm, Bool.true_and]
  · rw [decide_eq_false hm, Bool.false_and]
    rw [recB_congr n (g := fun _ => false) fun k _ => by
      rw [testBit_spr (hB k), decide_eq_false hm, Bool.false_and]]
    exact recB_false n

private theorem unpackP_spr {c : Nat → Nat} (hc : ∀ j, c j < 2 ^ 11) :
    unpackP (spr c 11) = (List.range 11).map c := by
  unfold unpackP
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_2047, testBit_spr hc]
  by_cases hi : i < 11
  · have h1 : (11 * j + i) / 11 = j := by omega
    have h2 : (11 * j + i) % 11 = i := by omega
    simp [h1, h2, hi, show 11 * j + i < 11 * 11 by omega]
  · simp [hi, Nat.testBit_lt_two_pow ((hc j).trans_le (Nat.pow_le_pow_right (by norm_num)
      (by omega : 11 ≤ i)))]

private theorem rowsXor_lt {r : Nat → Nat} {w : Nat} (m c : Nat) (h : ∀ k < m, r k < 2 ^ w) :
    rowsXor r m c < 2 ^ w := by
  rw [rowsXor_rec]
  refine recX_lt m fun k hk => ?_
  split
  · exact h k hk
  · exact Nat.two_pow_pos w

private theorem rec_eq_rowsXor {f r : Nat → Nat} {m c : Nat}
    (h : ∀ k < m, f k = if c.testBit k then r k else 0) :
    Nat.rec (motive := fun _ => Nat) 0 (fun k acc => acc ^^^ f k) m = rowsXor r m c := by
  rw [rowsXor_rec]
  exact recX_congr m h

private theorem rowsXor_congr {r r' : Nat → Nat} {m : Nat} (c : Nat) (h : ∀ k < m, r k = r' k) :
    rowsXor r m c = rowsXor r' m c := by
  rw [rowsXor_rec, rowsXor_rec]
  exact recX_congr m fun k hk => by rw [h k hk]

private theorem rowsXor_mulRec (r : Nat → Nat) (m c : Nat) :
    rowsXor r m c = Nat.rec (motive := fun _ => Nat) 0
      (fun k acc => Nat.xor acc (Nat.mul (Nat.land (Nat.shiftRight c k) 1) (r k))) m := by
  rw [rowsXor_rec]
  refine recX_congr m fun k _ => ?_
  change _ = (c >>> k &&& 1) * r k
  rw [shr_and_one]
  split <;> simp

private theorem actT_eq (p c : Nat) : actT (unpackP p) c = rowsXor (fldP p) 11 c :=
  rowsXor_congr c fun _ hk => getD_unpackP p hk

private theorem actT_lt (p c : Nat) : actT (unpackP p) c < 2 ^ 11 := by
  rw [actT_eq]
  exact rowsXor_lt 11 c fun k _ => fldP_lt p k

private theorem compB_eq (p q : Nat) :
    compB p q = spr (fun j => actT (unpackP p) ((unpackP q).getD j 0)) 11 := by
  have hB : ∀ k j, (if q.testBit (11 * j + k) then fldP p k else 0) < 2 ^ 11 := by
    intro k j
    split
    · exact fldP_lt p k
    · norm_num
  unfold compB
  simp only [Nat.xor_eq, Nat.land_eq, Nat.mul_eq, Nat.shiftRight_eq', compB_term]
  apply Nat.eq_of_testBit_eq
  intro m
  rw [testBit_rec_spr _ hB]
  congr 1
  refine spr_congr 11 fun j hj => ?_
  rw [getD_unpackP q hj, actT_eq]
  exact rec_eq_rowsXor fun k hk => by rw [testBit_fldP, decide_eq_true hk, Bool.true_and]

theorem compB_sound (p q : Nat) : unpackP (compB p q) = compT (unpackP p) (unpackP q) := by
  rw [compB_eq, unpackP_spr fun j => actT_lt p _]
  unfold compT
  apply List.ext_getElem (by simp [unpackP])
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h2), Option.getD_some]

theorem compB_lt (p q : Nat) : compB p q < 2 ^ 121 := by
  rw [compB_eq]
  exact spr_lt (fun j => actT_lt p _) 11

theorem actB_sound (p c : Nat) : actT (unpackP p) c = actB p c := by
  rw [actT_eq, rowsXor_mulRec]
  rfl

theorem unpackP_low (p : Nat) : unpackP (p % 2 ^ 121) = unpackP p := by
  unfold unpackP
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftRight,
    Nat.testBit_mod_two_pow, testBit_2047]
  by_cases hi : i < 11
  · simp [hi, show 11 * j + i < 121 by omega]
  · simp [hi]

theorem unpackP_inj {p q : Nat} (hp : p < 2 ^ 121) (hq : q < 2 ^ 121) (h : unpackP p = unpackP q) :
    p = q := by
  apply Nat.eq_of_testBit_eq
  intro n
  by_cases hn : n < 121
  · have hj : n / 11 < 11 := by omega
    have e := congrArg (fun l => (l.getD (n / 11) 0).testBit (n % 11)) h
    simp only [getD_unpackP _ hj, testBit_fldP, decide_eq_true (Nat.mod_lt n (by norm_num : 11 > 0)),
      Bool.true_and] at e
    rwa [Nat.div_add_mod] at e
  · rw [Nat.testBit_lt_two_pow (hp.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (hq.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))]

end CFSG.KC.J4Q

end
