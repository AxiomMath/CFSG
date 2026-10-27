module

public import Certificates.Data.Kernel.ShortVals
public import Certificates.Data.CFSGNative.YGroups.Y443.Witness
public import CFSG.Monster.AxisCount.DenseNative
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.LinearCombination
import CFSG.Certificates.Kernel.ShortVals.Distinct

public section

namespace CFSG.KC.ShortVals

open CFSG.YGroups.Y443Native CFSG.Monster.AxisCount.Native CFSG.Monster.B.Rep4371.Native
open Finset

abbrev MM : ℕ := 68719476736

@[expose] def Aent (i j : ℕ) : ℤ := (aTab ())[aIdx i j]!

theorem letK_eq (y : ℕ) (k : ℕ → Bool) : letK y k = k y := by
  cases y <;> rfl

theorem bitK_eq (w k : ℕ) : bitK w k = w.testBit k := by
  have h : bitK w k = (w >>> k &&& 1 == 1) := rfl
  rw [h, Nat.testBit, Nat.and_comm]
  cases Nat.mod_two_eq_zero_or_one (w >>> k) with
  | inl h0 => rw [Nat.one_and_eq_mod_two, h0]; rfl
  | inr h1 => rw [Nat.one_and_eq_mod_two, h1]; rfl

theorem nIf_eq (c : Bool) (t e : ℕ) : (Bool.rec (motive := fun _ => ℕ) e t c) =
    if c = true then t else e := by
  cases c <;> rfl

theorem bAnd_eq (a b : Bool) : (Bool.rec (motive := fun _ => Bool) false b a) = (a && b) := by
  cases a <;> rfl

theorem sumK_eq (n : ℕ) (f : ℕ → ℕ) : sumK n f = ∑ k ∈ range n, f k := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sum_range_succ, ← ih]
    rfl

theorem allK_eq (n : ℕ) (f : ℕ → Bool) : allK n f = true ↔ ∀ k < n, f k = true := by
  induction n with
  | zero => exact ⟨fun _ k hk => absurd hk (Nat.not_lt_zero k), fun _ => rfl⟩
  | succ n ih =>
    have e : allK (n + 1) f = (f n && allK n f) := bAnd_eq _ _
    rw [e, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
      · exact h2 k hk
      · exact hk ▸ h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun k hk => h k (Nat.lt_succ_of_lt hk)⟩

@[expose] def sgn (w k : ℕ) : ℤ := if w.testBit k then -1 else 1

theorem sgnK_cast (w k : ℕ) : ((sgnK w k : ℕ) : ZMod MM) = ((sgn w k : ℤ) : ZMod MM) := by
  have h : sgnK w k = if bitK w k = true then 68719476735 else 1 := nIf_eq _ _ _
  rw [h, bitK_eq]
  unfold sgn
  split
  · push_cast
    rw [eq_neg_iff_add_eq_zero]
    have : ((68719476735 : ℕ) : ZMod MM) + 1 = ((MM : ℕ) : ZMod MM) := by push_cast; rfl
    rw [ZMod.natCast_self] at this
    exact_mod_cast this
  · simp

theorem neg_cast (c : ℕ) : ((68719476736 * c - c : ℕ) : ZMod MM) = -(c : ZMod MM) := by
  rw [Nat.cast_sub (Nat.le_mul_of_pos_left c (by norm_num)), Nat.cast_mul, ZMod.natCast_self,
    zero_mul, zero_sub]

theorem bmK_get : ∀ j < 12, fld(bmK, Nat.mul 24 j, 16777215) = bmaskN j := by decide +kernel

theorem wordK_eq (a : ℕ) : wordK a = wordN a := by
  have key : ∀ n ≤ 12, Nat.rec (motive := fun _ => ℕ) 0 (fun j acc =>
      Bool.rec (motive := fun _ => ℕ) acc (Nat.xor acc (fld(bmK, Nat.mul 24 j, 16777215)))
        (bitK a j)) n = combN bmaskN n a := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      have e : combN bmaskN (n + 1) a = combN bmaskN n a ^^^ (if a.testBit n then bmaskN n else 0) :=
        rfl
      rw [e, ← ih (by omega)]
      change Bool.rec (motive := fun _ => ℕ) _ _ (bitK a n) = _
      rw [nIf_eq, bitK_eq]
      cases a.testBit n
      · simp
      · simp only [ite_true]
        rw [← bmK_get n (by omega)]
        rfl
  exact key 12 (Nat.le_refl _)

theorem sum_range_map (f : ℕ → ℤ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]
    simp

theorem aIdx_lt : ∀ i < 24, ∀ j < 24, aIdx i j < 300 := by decide +kernel

theorem aIdx_comm (i j : ℕ) : aIdx i j = aIdx j i := by
  unfold aIdx
  by_cases h : i = j
  · subst h
    rfl
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h), Nat.min_comm, Nat.max_comm]

theorem Aent_comm (i j : ℕ) : Aent i j = Aent j i := by
  unfold Aent
  rw [aIdx_comm]

theorem aFull_get (i j : ℕ) (hi : i < 24) (hj : j < 24) :
    (aFull (aV ()).D)[24 * i + j]! = Aent i j := by
  have hlt : 24 * i + j < 576 := by omega
  unfold aFull
  rw [getElem!_eq_getD', getD_ofFn _ _ hlt]
  have e1 : (24 * i + j) / 24 = i := by omega
  have e2 : (24 * i + j) % 24 = j := by omega
  simp only [e1, e2]
  have ha := aIdx_lt i hi j hj
  unfold aV
  rw [getElem!_eq_getD', getD_ofFn _ _ (by omega)]
  simp only [ha, ite_true]
  rfl

theorem qfN_A (u : Array ℤ) : qfN (aFull (aV ()).D) u =
    ∑ i ∈ range 24, ∑ j ∈ range 24, Aent i j * (u[i]! * u[j]!) := by
  unfold qfN
  rw [sum_range_map]
  refine sum_congr rfl fun i hi => ?_
  rw [sum_range_map]
  refine sum_congr rfl fun j hj => ?_
  rw [aFull_get i j (mem_range.1 hi) (mem_range.1 hj)]

theorem ofFn_get (f : Fin 24 → ℤ) (k : ℕ) (hk : k < 24) : (Array.ofFn f)[k]! = f ⟨k, hk⟩ := by
  rw [getElem!_pos _ _ (by simpa using hk)]
  simp

theorem shortVecN_F1 (p : ℕ) (hp : p < 552) (k : ℕ) (hk : k < 24) :
    (shortVecN p)[k]! = (if k = ((pairTab ())[p / 2]!).1 then 4 else 0) +
      (if k = ((pairTab ())[p / 2]!).2 then (if p % 2 = 0 then -4 else 4) else 0) := by
  unfold shortVecN
  rw [ite_eq_left hp]
  exact ofFn_get _ k hk

theorem shortVecN_F2 (p : ℕ) (h1 : 552 ≤ p) (h2 : p < 49704) (k : ℕ) (hk : k < 24) :
    (shortVecN p)[k]! = (if (wordN (2 * ((p - 552) / 24))).testBit k then -1 else 1) *
      (if k = (p - 552) % 24 then -3 else 1) := by
  unfold shortVecN
  rw [ite_eq_right (by omega), ite_eq_left h2]
  exact ofFn_get _ k hk

theorem shortVecN_F3 (p : ℕ) (h1 : 49704 ≤ p) (k : ℕ) (hk : k < 24) :
    (shortVecN p)[k]! = (if (wordN (octTab ())[(p - 49704) / 64]!).testBit k then 2 else 0) -
      (if (spreadG (wordN (octTab ())[(p - 49704) / 64]!) (evenTab ())[(p - 49704) % 64]!).testBit
        k then 4 else 0) := by
  unfold shortVecN
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  exact ofFn_get _ k hk

theorem qf_sub (A : ℕ → ℕ → ℤ) (n : ℕ) (u g : ℕ → ℤ) :
    ∑ j ∈ range n, ∑ k ∈ range n, A j k * ((u j - g j) * (u k - g k)) =
      ∑ j ∈ range n, ∑ k ∈ range n, A j k * (u j * u k) -
      ∑ j ∈ range n, ∑ k ∈ range n, A j k * (u j * g k) -
      ∑ j ∈ range n, ∑ k ∈ range n, A j k * (g j * u k) +
      ∑ j ∈ range n, ∑ k ∈ range n, A j k * (g j * g k) := by
  have e : ∀ j k, A j k * ((u j - g j) * (u k - g k)) = A j k * (u j * u k) -
      A j k * (u j * g k) - A j k * (g j * u k) + A j k * (g j * g k) := by
    intro j k
    ring
  simp only [e, sum_add_distrib, sum_sub_distrib]

theorem sum_mul_ite (n c : ℕ) (hc : c < n) (F : ℕ → ℤ) (y : ℤ) :
    ∑ k ∈ range n, F k * (if k = c then y else 0) = F c * y := by
  simp only [mul_ite, mul_zero, sum_ite_eq', mem_range, hc, ite_true]

theorem sum_ite_mul (n c : ℕ) (hc : c < n) (F : ℕ → ℤ) (y : ℤ) :
    ∑ k ∈ range n, (if k = c then y else 0) * F k = y * F c := by
  simp only [ite_mul, zero_mul, sum_ite_eq', mem_range, hc, ite_true]

theorem sum_delta2 (A : ℕ → ℕ → ℤ) (n a c : ℕ) (ha : a < n) (hc : c < n) (x y : ℤ) :
    ∑ j ∈ range n, ∑ k ∈ range n, A j k * ((if j = a then x else 0) * (if k = c then y else 0)) =
      x * y * A a c := by
  have e : ∀ j, ∑ k ∈ range n, A j k * ((if j = a then x else 0) * (if k = c then y else 0)) =
      (if j = a then x else 0) * (A j c * y) := by
    intro j
    have e' : ∑ k ∈ range n, A j k * ((if j = a then x else 0) * (if k = c then y else 0)) =
        ∑ k ∈ range n, (A j k * (if j = a then x else 0)) * (if k = c then y else 0) :=
      sum_congr rfl fun k _ => by ring
    rw [e', sum_mul_ite n c hc (fun k => A j k * (if j = a then x else 0)) y]
    ring
  rw [sum_congr rfl fun j _ => e j, sum_ite_mul n a ha]
  ring

theorem sum_delta_r (A : ℕ → ℕ → ℤ) (n c : ℕ) (hc : c < n) (f : ℕ → ℤ) (y : ℤ) :
    ∑ j ∈ range n, ∑ k ∈ range n, A j k * (f j * (if k = c then y else 0)) =
      y * ∑ j ∈ range n, A j c * f j := by
  rw [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  have e : ∑ k ∈ range n, A j k * (f j * (if k = c then y else 0)) =
      ∑ k ∈ range n, (A j k * f j) * (if k = c then y else 0) :=
    sum_congr rfl fun k _ => by ring
  rw [e, sum_mul_ite n c hc (fun k => A j k * f j) y]
  ring

theorem sum_delta_l (A : ℕ → ℕ → ℤ) (n c : ℕ) (hc : c < n) (f : ℕ → ℤ) (y : ℤ) :
    ∑ j ∈ range n, ∑ k ∈ range n, A j k * ((if j = c then y else 0) * f k) =
      y * ∑ k ∈ range n, A c k * f k := by
  have e : ∀ j, ∑ k ∈ range n, A j k * ((if j = c then y else 0) * f k) =
      (if j = c then y else 0) * ∑ k ∈ range n, A j k * f k := by
    intro j
    rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    ring
  rw [sum_congr rfl fun j _ => e j, sum_ite_mul n c hc]

theorem pair_alg (A : ℕ → ℕ → ℤ) (a c : ℕ) (ha : a < 24) (hc : c < 24) (x y : ℤ) :
    ∑ j ∈ range 24, ∑ k ∈ range 24, A j k *
      (((if j = a then x else 0) + (if j = c then y else 0)) *
        ((if k = a then x else 0) + (if k = c then y else 0))) =
      x * x * A a a + x * y * A a c + y * x * A c a + y * y * A c c := by
  have e : ∀ j k, A j k * (((if j = a then x else 0) + (if j = c then y else 0)) *
      ((if k = a then x else 0) + (if k = c then y else 0))) =
      A j k * ((if j = a then x else 0) * (if k = a then x else 0)) +
      A j k * ((if j = a then x else 0) * (if k = c then y else 0)) +
      A j k * ((if j = c then y else 0) * (if k = a then x else 0)) +
      A j k * ((if j = c then y else 0) * (if k = c then y else 0)) := by
    intro j k
    ring
  simp only [e, sum_add_distrib]
  rw [sum_delta2 A 24 a a ha ha, sum_delta2 A 24 a c ha hc, sum_delta2 A 24 c a hc ha,
    sum_delta2 A 24 c c hc hc]

theorem odd_alg (A : ℕ → ℕ → ℤ) (hA : ∀ j k, A j k = A k j) (s : ℕ → ℤ)
    (hs : ∀ k, s k * s k = 1) (i : ℕ) (hi : i < 24) :
    ∑ j ∈ range 24, ∑ k ∈ range 24, A j k *
      ((s j * (if j = i then -3 else 1)) * (s k * (if k = i then -3 else 1))) =
      (∑ j ∈ range 24, s j * ∑ k ∈ range 24, A j k * s k) -
        8 * s i * (∑ k ∈ range 24, A i k * s k) + 16 * A i i := by
  have e : ∀ j, s j * (if j = i then -3 else 1) = s j - (if j = i then 4 * s i else 0) := by
    intro j
    by_cases h : j = i
    · subst h
      simp only [ite_true]
      ring
    · simp only [h, ite_false]
      ring
  simp only [e]
  rw [qf_sub A 24 s (fun j => if j = i then 4 * s i else 0), sum_delta_r A 24 i hi,
    sum_delta_l A 24 i hi, sum_delta2 A 24 i i hi hi]
  have h1 : ∑ j ∈ range 24, ∑ k ∈ range 24, A j k * (s j * s k) =
      ∑ j ∈ range 24, s j * ∑ k ∈ range 24, A j k * s k := by
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    ring
  have h2 : ∑ j ∈ range 24, A j i * s j = ∑ k ∈ range 24, A i k * s k :=
    sum_congr rfl fun k _ => by rw [hA]
  rw [h1, h2]
  have := hs i
  linear_combination (16 * A i i) * this

theorem oct_alg (A : ℕ → ℕ → ℤ) (hA : ∀ j k, A j k = A k j) (bw bd : ℕ → Bool) :
    ∑ j ∈ range 24, ∑ k ∈ range 24, A j k *
      (((if bw j = true then 2 else 0) - (if bd j = true then 4 else 0)) *
        ((if bw k = true then 2 else 0) - (if bd k = true then 4 else 0))) =
      4 * (∑ k ∈ range 24, if bw k = true then ∑ j ∈ range 24, (if bw j = true then A k j else 0)
          else 0) -
      16 * (∑ k ∈ range 24, if bd k = true then ∑ j ∈ range 24, (if bw j = true then A k j else 0)
          else 0) +
      16 * (∑ j ∈ range 24, if bd j = true then ∑ k ∈ range 24, (if bd k = true then A j k else 0)
          else 0) := by
  rw [qf_sub A 24 (fun j => if bw j = true then 2 else 0) (fun j => if bd j = true then 4 else 0)]
  have hW : ∑ j ∈ range 24, ∑ k ∈ range 24, A j k *
      ((if bw j = true then 2 else 0) * (if bw k = true then 2 else 0)) =
      4 * (∑ k ∈ range 24, if bw k = true then ∑ j ∈ range 24, (if bw j = true then A k j else 0)
        else 0) := by
    rw [mul_sum, sum_comm]
    refine sum_congr rfl fun k _ => ?_
    rw [apply_ite (4 * ·), mul_sum, mul_zero]
    by_cases hk : bw k = true
    · simp only [hk, ite_true]
      refine sum_congr rfl fun j _ => ?_
      rw [hA]
      by_cases hj : bw j = true
      · simp only [hj, ite_true]
        ring
      · simp [hj]
    · simp [hk]
  have hX1 : ∑ j ∈ range 24, ∑ k ∈ range 24, A j k *
      ((if bw j = true then 2 else 0) * (if bd k = true then 4 else 0)) =
      8 * (∑ k ∈ range 24, if bd k = true then ∑ j ∈ range 24, (if bw j = true then A k j else 0)
        else 0) := by
    rw [mul_sum, sum_comm]
    refine sum_congr rfl fun k _ => ?_
    rw [apply_ite (8 * ·), mul_sum, mul_zero]
    by_cases hk : bd k = true
    · simp only [hk, ite_true]
      refine sum_congr rfl fun j _ => ?_
      rw [hA]
      by_cases hj : bw j = true
      · simp only [hj, ite_true]
        ring
      · simp [hj]
    · simp [hk]
  have hX2 : ∑ j ∈ range 24, ∑ k ∈ range 24, A j k *
      ((if bd j = true then 4 else 0) * (if bw k = true then 2 else 0)) =
      8 * (∑ k ∈ range 24, if bd k = true then ∑ j ∈ range 24, (if bw j = true then A k j else 0)
        else 0) := by
    rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [apply_ite (8 * ·), mul_sum, mul_zero]
    by_cases hk : bd k = true
    · simp only [hk, ite_true]
      refine sum_congr rfl fun j _ => ?_
      by_cases hj : bw j = true
      · simp only [hj, ite_true]
        ring
      · simp [hj]
    · simp [hk]
  have hY : ∑ j ∈ range 24, ∑ k ∈ range 24, A j k *
      ((if bd j = true then 4 else 0) * (if bd k = true then 4 else 0)) =
      16 * (∑ j ∈ range 24, if bd j = true then ∑ k ∈ range 24, (if bd k = true then A j k else 0)
        else 0) := by
    rw [mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [apply_ite (16 * ·), mul_sum, mul_zero]
    by_cases hj : bd j = true
    · simp only [hj, ite_true]
      refine sum_congr rfl fun k _ => ?_
      by_cases hk : bd k = true
      · simp only [hk, ite_true]
        ring
      · simp [hk]
    · simp [hj]
  rw [hW, hX1, hX2, hY]
  ring

theorem sgn_mul_self (w k : ℕ) : sgn w k * sgn w k = 1 := by
  unfold sgn
  split <;> norm_num

theorem modMM_cast (x : ℕ) : (((x % 68719476736 : ℕ)) : ZMod MM) = (x : ZMod MM) :=
  ZMod.natCast_mod x MM

theorem lit8 : ((549755813880 : ℕ) : ZMod MM) = -8 := by
  have h : (549755813880 : ℕ) = 68719476736 * 8 - 8 := by norm_num
  rw [h, neg_cast]
  norm_num

theorem lit16 : ((1099511627760 : ℕ) : ZMod MM) = -16 := by
  have h : (1099511627760 : ℕ) = 68719476736 * 16 - 16 := by norm_num
  rw [h, neg_cast]
  norm_num

theorem lit32 : ((2199023255520 : ℕ) : ZMod MM) = -32 := by
  have h : (2199023255520 : ℕ) = 68719476736 * 32 - 32 := by norm_num
  rw [h, neg_cast]
  norm_num

section Tables

variable (AP : ℕ) (hA : ∀ i < 24, ∀ j < 24, ((aK AP i j : ℕ) : ℤ) = Aent i j)
include hA

theorem aK_cast {i j : ℕ} (hi : i < 24) (hj : j < 24) :
    ((aK AP i j : ℕ) : ZMod MM) = ((Aent i j : ℤ) : ZMod MM) := by
  rw [← hA i hi j hj, Int.cast_natCast]

theorem asK_cast (w : ℕ) {i : ℕ} (hi : i < 24) :
    ((asK AP w i : ℕ) : ZMod MM) = ((∑ k ∈ range 24, Aent i k * sgn w k : ℤ) : ZMod MM) := by
  have e : asK AP w i = ∑ k ∈ range 24, aK AP i k * sgnK w k := sumK_eq _ _
  rw [e]
  push_cast
  refine sum_congr rfl fun k hk => ?_
  rw [aK_cast AP hA hi (mem_range.1 hk), sgnK_cast]

theorem qK_cast (w : ℕ) : ((qK AP w : ℕ) : ZMod MM) =
    ((∑ j ∈ range 24, sgn w j * ∑ k ∈ range 24, Aent j k * sgn w k : ℤ) : ZMod MM) := by
  have e : qK AP w = ∑ i ∈ range 24, sgnK w i * asK AP w i := sumK_eq _ _
  rw [e]
  push_cast
  refine sum_congr rfl fun i hi => ?_
  rw [sgnK_cast, asK_cast AP hA w (mem_range.1 hi)]
  push_cast
  ring

theorem eOdd_cast (w : ℕ) {i : ℕ} (hi : i < 24) :
    ((eOdd AP w (qK AP w) i : ℕ) : ZMod MM) =
      (((∑ j ∈ range 24, sgn w j * ∑ k ∈ range 24, Aent j k * sgn w k) -
        8 * sgn w i * (∑ k ∈ range 24, Aent i k * sgn w k) + 16 * Aent i i : ℤ) : ZMod MM) := by
  have e : eOdd AP w (qK AP w) i =
      (qK AP w + 549755813880 * (sgnK w i * asK AP w i) + 16 * aK AP i i) % 68719476736 := rfl
  rw [e, modMM_cast, Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, lit8,
    qK_cast AP hA, sgnK_cast, asK_cast AP hA w hi, aK_cast AP hA hi hi]
  push_cast
  ring

theorem awK_cast (w : ℕ) {k : ℕ} (hk : k < 24) :
    ((awK AP w k : ℕ) : ZMod MM) =
      ((∑ j ∈ range 24, (if w.testBit j = true then Aent k j else 0) : ℤ) : ZMod MM) := by
  have e : awK AP w k = ∑ j ∈ range 24,
      (Bool.rec (motive := fun _ => ℕ) 0 (aK AP k j) (bitK w j)) := sumK_eq _ _
  rw [e]
  push_cast
  refine sum_congr rfl fun j hj => ?_
  rw [nIf_eq, bitK_eq]
  split
  · rw [aK_cast AP hA hk (mem_range.1 hj)]
  · simp

theorem wwK_cast (w : ℕ) : ((wwK AP w : ℕ) : ZMod MM) =
    ((∑ k ∈ range 24, if w.testBit k = true then
      ∑ j ∈ range 24, (if w.testBit j = true then Aent k j else 0) else 0 : ℤ) : ZMod MM) := by
  have e : wwK AP w = ∑ k ∈ range 24,
      (Bool.rec (motive := fun _ => ℕ) 0 (awK AP w k) (bitK w k)) := sumK_eq _ _
  rw [e]
  push_cast
  refine sum_congr rfl fun k hk => ?_
  rw [nIf_eq, bitK_eq]
  split
  · rw [awK_cast AP hA w (mem_range.1 hk)]
    push_cast
    rfl
  · simp

theorem xK8_cast (OC o w m : ℕ) (hc : ∀ a < 8, cAt OC o a < 24) :
    ((xK8 AP OC o w m : ℕ) : ZMod MM) =
      ((∑ a ∈ range 8, if m.testBit a = true then
        ∑ j ∈ range 24, (if w.testBit j = true then Aent (cAt OC o a) j else 0) else 0 : ℤ) :
        ZMod MM) := by
  have e : xK8 AP OC o w m = ∑ a ∈ range 8,
      (Bool.rec (motive := fun _ => ℕ) 0 (awK AP w (cAt OC o a)) (bitK m a)) := sumK_eq _ _
  rw [e]
  push_cast
  refine sum_congr rfl fun a ha => ?_
  rw [nIf_eq, bitK_eq]
  split
  · rw [awK_cast AP hA w (hc a (mem_range.1 ha))]
    push_cast
    rfl
  · simp

theorem yK8_cast (OC o m : ℕ) (hc : ∀ a < 8, cAt OC o a < 24) :
    ((yK8 AP OC o m : ℕ) : ZMod MM) =
      ((∑ a ∈ range 8, if m.testBit a = true then
        ∑ b ∈ range 8, (if m.testBit b = true then Aent (cAt OC o a) (cAt OC o b) else 0)
          else 0 : ℤ) : ZMod MM) := by
  have e : yK8 AP OC o m = ∑ a ∈ range 8, (Bool.rec (motive := fun _ => ℕ) 0
      (∑ b ∈ range 8, Bool.rec (motive := fun _ => ℕ) 0 (aK AP (cAt OC o a) (cAt OC o b))
        (bitK m b)) (bitK m a)) := by
    unfold yK8
    rw [sumK_eq]
    refine sum_congr rfl fun a _ => ?_
    rw [sumK_eq]
  rw [e]
  push_cast
  refine sum_congr rfl fun a ha => ?_
  rw [nIf_eq, bitK_eq]
  split
  · push_cast
    refine sum_congr rfl fun b hb => ?_
    rw [nIf_eq, bitK_eq]
    split
    · rw [aK_cast AP hA (hc a (mem_range.1 ha)) (hc b (mem_range.1 hb))]
    · simp
  · simp

end Tables

theorem combN_congr' (f g : ℕ → ℕ) (m : ℕ) :
    ∀ n, (∀ t < n, f t = g t) → combN f n m = combN g n m := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    have e1 : combN f (n + 1) m = combN f n m ^^^ (if m.testBit n then f n else 0) := rfl
    have e2 : combN g (n + 1) m = combN g n m ^^^ (if m.testBit n then g n else 0) := rfl
    rw [e1, e2, ih fun t ht => h t (by omega), h n (by omega)]

theorem combN_testBit (c : ℕ → ℕ) (hinj : ∀ a < 8, ∀ b < 8, c a = c b → a = b) (m k : ℕ) :
    ∀ n ≤ 8, ((combN (fun t => 2 ^ c t) n m).testBit k = true ↔
      ∃ a < n, m.testBit a = true ∧ c a = k) := by
  intro n
  induction n with
  | zero => intro _; simp [combN]
  | succ n ih =>
    intro hn
    have e : combN (fun t => 2 ^ c t) (n + 1) m =
        combN (fun t => 2 ^ c t) n m ^^^ (if m.testBit n then 2 ^ c n else 0) := rfl
    rw [e, Nat.testBit_xor]
    have ih' := ih (by omega)
    by_cases hb : m.testBit n = true
    · rw [ite_eq_left hb, Nat.testBit_two_pow]
      by_cases hk : c n = k
      · have hno : (combN (fun t => 2 ^ c t) n m).testBit k = false := by
          cases h : (combN (fun t => 2 ^ c t) n m).testBit k
          · rfl
          · obtain ⟨a, ha, -, hca⟩ := ih'.1 h
            have := hinj a (by omega) n (by omega) (hca.trans hk.symm)
            omega
        rw [hno, decide_eq_true hk]
        exact ⟨fun _ => ⟨n, Nat.lt_succ_self n, hb, hk⟩, fun _ => rfl⟩
      · rw [decide_eq_false hk, Bool.xor_false, ih']
        constructor
        · rintro ⟨a, ha, h1, h2⟩
          exact ⟨a, by omega, h1, h2⟩
        · rintro ⟨a, ha, h1, h2⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | ha
          · exact ⟨a, ha, h1, h2⟩
          · subst ha
            exact absurd h2 hk
    · have hb' : m.testBit n = false := by simpa using hb
      rw [ite_eq_right hb, Nat.zero_testBit, Bool.xor_false, ih']
      constructor
      · rintro ⟨a, ha, h1, h2⟩
        exact ⟨a, by omega, h1, h2⟩
      · rintro ⟨a, ha, h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | ha
        · exact ⟨a, ha, h1, h2⟩
        · subst ha
          rw [hb'] at h1
          exact absurd h1 Bool.false_ne_true

theorem sum_reindex (c : ℕ → ℕ) (hinj : ∀ a < 8, ∀ b < 8, c a = c b → a = b)
    (hlt : ∀ a < 8, c a < 24) (m : ℕ) (F : ℕ → ℤ) :
    ∑ k ∈ range 24, (if (combN (fun t => 2 ^ c t) 8 m).testBit k = true then F k else 0) =
      ∑ a ∈ range 8, (if m.testBit a = true then F (c a) else 0) := by
  rw [← sum_filter, ← sum_filter]
  have hset : (range 24).filter (fun k => (combN (fun t => 2 ^ c t) 8 m).testBit k = true) =
      ((range 8).filter (fun a => m.testBit a = true)).image c := by
    ext k
    simp only [mem_filter, mem_range, mem_image, combN_testBit c hinj m k 8 (Nat.le_refl _)]
    constructor
    · rintro ⟨-, a, ha, h1, h2⟩
      exact ⟨a, ⟨ha, h1⟩, h2⟩
    · rintro ⟨a, ⟨ha, h1⟩, h2⟩
      exact ⟨h2 ▸ hlt a ha, a, ha, h1, h2⟩
  rw [hset, sum_image]
  intro a ha b hb e
  simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at ha hb
  exact hinj a ha.1 b hb.1 e

theorem coords_spec (w : ℕ) (c : ℕ → ℕ) (hs : suppList w = (List.range 8).map c) :
    (∀ a < 8, ∀ b < 8, c a = c b → a = b) ∧ (∀ a < 8, c a < 24) := by
  have hnd : ((List.range 8).map c).Nodup := by
    rw [← hs]
    exact List.nodup_range.filter _
  refine ⟨fun a ha b hb e => ?_, fun a ha => ?_⟩
  · exact List.inj_on_of_nodup_map hnd (List.mem_range.2 ha) (List.mem_range.2 hb) e
  · have hm : c a ∈ suppList w := by
      rw [hs]
      exact List.mem_map.2 ⟨a, List.mem_range.2 ha, rfl⟩
    unfold suppList at hm
    exact List.mem_range.1 (List.mem_filter.1 hm).1

theorem spreadG_eq (w m : ℕ) (c : ℕ → ℕ) (hs : suppList w = (List.range 8).map c) :
    spreadG w m = combN (fun t => 2 ^ c t) 8 m := by
  unfold spreadG
  refine combN_congr' _ _ m 8 fun t ht => ?_
  rw [hs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht]
  rfl

theorem eOdd_lt (AP w Q i : ℕ) : eOdd AP w Q i < MM := Nat.mod_lt _ (by norm_num)

theorem eOct_lt (W X Y : ℕ) : eOct W X Y < MM := Nat.mod_lt _ (by norm_num)

theorem odd_val (AP WT : ℕ) (hA : ∀ i < 24, ∀ j < 24, ((aK AP i j : ℕ) : ℤ) = Aent i j)
    (hW : ∀ t < 2048, wAt WT t = wordN (2 * t)) {t i : ℕ} (ht : t < 2048) (hi : i < 24) :
    ((eOdd AP (wAt WT t) (qK AP (wAt WT t)) i : ℕ) : ZMod MM) =
      ((qfN (aFull (aV ()).D) (shortVecN (552 + 24 * t + i)) : ℤ) : ZMod MM) := by
  rw [eOdd_cast AP hA _ hi, qfN_A]
  refine congrArg (Int.cast : ℤ → ZMod MM) ?_
  have e1 : (552 + 24 * t + i - 552) / 24 = t := by omega
  have e2 : (552 + 24 * t + i - 552) % 24 = i := by omega
  have hu : ∀ k ∈ range 24, (shortVecN (552 + 24 * t + i))[k]! =
      sgn (wAt WT t) k * (if k = i then -3 else 1) := by
    intro k hk
    rw [shortVecN_F2 _ (by omega) (by omega) k (mem_range.1 hk), e1, e2, hW t ht]
    rfl
  rw [← odd_alg Aent Aent_comm (sgn (wAt WT t)) (sgn_mul_self _) i hi]
  refine sum_congr rfl fun j hj => sum_congr rfl fun k hk => ?_
  rw [hu j hj, hu k hk]

theorem oct_val (AP OWT OC ET : ℕ) (hA : ∀ i < 24, ∀ j < 24, ((aK AP i j : ℕ) : ℤ) = Aent i j)
    (hOW : ∀ o < 759, wAt OWT o = wordN (octTab ())[o]!)
    (hOC : ∀ o < 759, suppList (wordN (octTab ())[o]!) = (List.range 8).map (cAt OC o))
    (hET : ∀ m < 64, eAt ET m = (evenTab ())[m]!) {o m : ℕ} (ho : o < 759) (hm : m < 64) :
    ((eOct (wwK AP (wAt OWT o)) (xK8 AP OC o (wAt OWT o) (eAt ET m)) (yK8 AP OC o (eAt ET m)) :
        ℕ) : ZMod MM) =
      ((qfN (aFull (aV ()).D) (shortVecN (49704 + 64 * o + m)) : ℤ) : ZMod MM) := by
  obtain ⟨hinj, hlt⟩ := coords_spec _ _ (hOC o ho)
  have hd := spreadG_eq (wordN (octTab ())[o]!) (evenTab ())[m]! _ (hOC o ho)
  have e : eOct (wwK AP (wAt OWT o)) (xK8 AP OC o (wAt OWT o) (eAt ET m)) (yK8 AP OC o (eAt ET m))
      = (4 * wwK AP (wAt OWT o) + 1099511627760 * xK8 AP OC o (wAt OWT o) (eAt ET m) +
        16 * yK8 AP OC o (eAt ET m)) % 68719476736 := rfl
  rw [e, modMM_cast, Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, lit16,
    wwK_cast AP hA, xK8_cast AP hA _ _ _ _ hlt, yK8_cast AP hA _ _ _ hlt, hOW o ho, hET m hm, qfN_A]
  have e1 : (49704 + 64 * o + m - 49704) / 64 = o := by omega
  have e2 : (49704 + 64 * o + m - 49704) % 64 = m := by omega
  have hu : ∀ k ∈ range 24, (shortVecN (49704 + 64 * o + m))[k]! =
      (if (wordN (octTab ())[o]!).testBit k = true then 2 else 0) -
        (if (spreadG (wordN (octTab ())[o]!) (evenTab ())[m]!).testBit k = true then 4 else 0) := by
    intro k hk
    rw [shortVecN_F3 _ (by omega) k (mem_range.1 hk), e1, e2]
  rw [sum_congr rfl fun j hj => sum_congr rfl fun k hk => by rw [hu j hj, hu k hk],
    oct_alg Aent Aent_comm, hd]
  simp only [sum_reindex _ hinj hlt]
  push_cast
  ring

theorem pair_val (AP PT : ℕ) (hA : ∀ i < 24, ∀ j < 24, ((aK AP i j : ℕ) : ℤ) = Aent i j)
    (hPT : ∀ q < 276, pAt PT q 0 = ((pairTab ())[q]!).1 ∧ pAt PT q 1 = ((pairTab ())[q]!).2 ∧
      ((pairTab ())[q]!).1 < 24 ∧ ((pairTab ())[q]!).2 < 24) {q : ℕ} (hq : q < 276) :
    (((16 * aK AP (pAt PT q 0) (pAt PT q 0) + 16 * aK AP (pAt PT q 1) (pAt PT q 1) +
        2199023255520 * aK AP (pAt PT q 0) (pAt PT q 1)) % 68719476736 : ℕ) : ZMod MM) =
      ((qfN (aFull (aV ()).D) (shortVecN (2 * q)) : ℤ) : ZMod MM) ∧
    (((16 * aK AP (pAt PT q 0) (pAt PT q 0) + 16 * aK AP (pAt PT q 1) (pAt PT q 1) +
        32 * aK AP (pAt PT q 0) (pAt PT q 1)) % 68719476736 : ℕ) : ZMod MM) =
      ((qfN (aFull (aV ()).D) (shortVecN (2 * q + 1)) : ℤ) : ZMod MM) := by
  obtain ⟨h0, h1, ha, hc⟩ := hPT q hq
  rw [h0, h1]
  have key : ∀ p, p / 2 = q → qfN (aFull (aV ()).D) (shortVecN p) =
      16 * Aent (pairTab ())[q]!.1 (pairTab ())[q]!.1 +
        16 * Aent (pairTab ())[q]!.2 (pairTab ())[q]!.2 +
        8 * (if p % 2 = 0 then -4 else 4) * Aent (pairTab ())[q]!.1 (pairTab ())[q]!.2 := by
    intro p hp
    rw [qfN_A]
    have hu : ∀ k ∈ range 24, (shortVecN p)[k]! =
        (if k = ((pairTab ())[q]!).1 then 4 else 0) +
          (if k = ((pairTab ())[q]!).2 then (if p % 2 = 0 then -4 else 4) else 0) := by
      intro k hk
      rw [shortVecN_F1 p (by omega) k (mem_range.1 hk), hp]
    rw [sum_congr rfl fun j hj => sum_congr rfl fun k hk => by rw [hu j hj, hu k hk],
      pair_alg Aent _ _ ha hc, Aent_comm ((pairTab ())[q]!).2]
    split <;> ring
  refine ⟨?_, ?_⟩
  · rw [key (2 * q) (by omega), modMM_cast, Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul,
      Nat.cast_mul, lit32, aK_cast AP hA ha ha, aK_cast AP hA hc hc, aK_cast AP hA ha hc]
    simp only [Nat.mul_mod_right, ite_true]
    push_cast
    ring
  · rw [key (2 * q + 1) (by omega), modMM_cast, Nat.cast_add, Nat.cast_add, Nat.cast_mul,
      Nat.cast_mul, Nat.cast_mul, aK_cast AP hA ha ha, aK_cast AP hA hc hc, aK_cast AP hA ha hc]
    have : (2 * q + 1) % 2 ≠ 0 := by omega
    simp only [this, ite_false]
    push_cast
    ring

theorem posOK_spec {VP RP PP p e : ℕ} (h : posOK VP RP PP p e = true) :
    rAt RP p < 98280 ∧ e = vAt VP (rAt RP p) ∧ rAt PP (rAt RP p) = p := by
  unfold posOK at h
  simpa only [letK_eq, bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] using h

theorem vAt_strict {VP : ℕ} (h : ∀ k < 98279, incOK VP k = true) :
    ∀ d k, k + d + 1 < 98280 → vAt VP k < vAt VP (k + d + 1) := by
  intro d
  induction d with
  | zero =>
    intro k hk
    have := h k (by omega)
    unfold incOK at this
    simpa only [Nat.blt_eq] using this
  | succ d ih =>
    intro k hk
    have h1 := ih k (by omega)
    have h2 := h (k + d + 1) (by omega)
    unfold incOK at h2
    rw [Nat.blt_eq] at h2
    exact Nat.lt_trans h1 h2

theorem vAt_inj {VP : ℕ} (h : ∀ k < 98279, incOK VP k = true) {k l : ℕ} (hk : k < 98280)
    (hl : l < 98280) (e : vAt VP k = vAt VP l) : k = l := by
  rcases Nat.lt_trichotomy k l with hkl | hkl | hkl
  · have := vAt_strict h (l - k - 1) k (by omega)
    have el : k + (l - k - 1) + 1 = l := by omega
    rw [el] at this
    omega
  · exact hkl
  · have := vAt_strict h (k - l - 1) l (by omega)
    have ek : l + (k - l - 1) + 1 = k := by omega
    rw [ek] at this
    omega

theorem shortValsN_size' (A : Array ℤ) : (shortValsN A).size = 98280 := by
  simp [shortValsN]

theorem shortValsN_get' (A : Array ℤ) (p : ℕ) (hp : p < 98280) :
    (shortValsN A)[p]! = qfN A (shortVecN p) := by
  rw [getElem!_pos _ _ (by rw [shortValsN_size']; exact hp)]
  simp [shortValsN]

theorem shortValsOK_of_checks (AP WT OWT OC ET PT VP RP PP : ℕ)
    (hA : ∀ i < 24, ∀ j < 24, ((aK AP i j : ℕ) : ℤ) = Aent i j)
    (hW : ∀ t < 2048, wAt WT t = wordN (2 * t))
    (hOW : ∀ o < 759, wAt OWT o = wordN (octTab ())[o]!)
    (hOC : ∀ o < 759, suppList (wordN (octTab ())[o]!) = (List.range 8).map (cAt OC o))
    (hET : ∀ m < 64, eAt ET m = (evenTab ())[m]!)
    (hPT : ∀ q < 276, pAt PT q 0 = ((pairTab ())[q]!).1 ∧ pAt PT q 1 = ((pairTab ())[q]!).2 ∧
      ((pairTab ())[q]!).1 < 24 ∧ ((pairTab ())[q]!).2 < 24)
    (hPair : ∀ q < 276, pairOK AP PT VP RP PP q = true)
    (hOdd : ∀ t < 2048, oddOK AP WT VP RP PP t = true)
    (hOct : ∀ o < 759, octOK AP OWT OC ET VP RP PP o = true)
    (hInc : ∀ k < 98279, incOK VP k = true) :
    shortValsOK () = true := by
  have hpos : ∀ p < 98280, ∃ e, e < MM ∧
      ((e : ℕ) : ZMod MM) = ((qfN (aFull (aV ()).D) (shortVecN p) : ℤ) : ZMod MM) ∧
      posOK VP RP PP p e = true := by
    intro p hp
    by_cases h1 : p < 552
    · have hq : p / 2 < 276 := by omega
      have hc := hPair (p / 2) hq
      unfold pairOK at hc
      simp only [letK_eq, bAnd_eq, Bool.and_eq_true] at hc
      obtain ⟨v0, v1⟩ := pair_val AP PT hA hPT hq
      rcases Nat.mod_two_eq_zero_or_one p with h | h
      · have e : 2 * (p / 2) = p := by omega
        have e' : Nat.mul 2 (p / 2) = p := e
        rw [e] at v0
        rw [e'] at hc
        exact ⟨_, Nat.mod_lt _ (by norm_num), v0, hc.1⟩
      · have e : 2 * (p / 2) + 1 = p := by omega
        have e' : (Nat.mul 2 (p / 2)).add 1 = p := e
        rw [e] at v1
        rw [e'] at hc
        exact ⟨_, Nat.mod_lt _ (by norm_num), v1, hc.2⟩
    by_cases h2 : p < 49704
    · have ht : (p - 552) / 24 < 2048 := by omega
      have hi : (p - 552) % 24 < 24 := Nat.mod_lt _ (by norm_num)
      have hc := hOdd _ ht
      unfold oddOK at hc
      rw [letK_eq, letK_eq, allK_eq] at hc
      have e : 552 + 24 * ((p - 552) / 24) + (p - 552) % 24 = p := by omega
      have e' : Nat.add (Nat.add 552 (Nat.mul 24 ((p - 552) / 24))) ((p - 552) % 24) = p := e
      have v := odd_val AP WT hA hW ht hi
      rw [e] at v
      have hc' := hc _ hi
      rw [e'] at hc'
      exact ⟨_, eOdd_lt _ _ _ _, v, hc'⟩
    · have ho : (p - 49704) / 64 < 759 := by omega
      have hm : (p - 49704) % 64 < 64 := Nat.mod_lt _ (by norm_num)
      have hc := hOct _ ho
      unfold octOK at hc
      rw [letK_eq, letK_eq, allK_eq] at hc
      have hc' := hc _ hm
      rw [letK_eq] at hc'
      have e : 49704 + 64 * ((p - 49704) / 64) + (p - 49704) % 64 = p := by omega
      have e' : Nat.add (Nat.add 49704 (Nat.mul 64 ((p - 49704) / 64))) ((p - 49704) % 64) = p := e
      have v := oct_val AP OWT OC ET hA hOW hOC hET ho hm
      rw [e] at v
      rw [e'] at hc'
      exact ⟨_, eOct_lt _ _ _, v, hc'⟩
  have hinj : ∀ p q, p < 98280 → q < 98280 →
      qfN (aFull (aV ()).D) (shortVecN p) = qfN (aFull (aV ()).D) (shortVecN q) → p = q := by
    intro p q hp hq hpq
    obtain ⟨ep, hep, cp, op⟩ := hpos p hp
    obtain ⟨eq, heq, cq, oq⟩ := hpos q hq
    obtain ⟨rp, vp, ip⟩ := posOK_spec op
    obtain ⟨rq, vq, iq⟩ := posOK_spec oq
    have hc : ((ep : ℕ) : ZMod MM) = ((eq : ℕ) : ZMod MM) := by rw [cp, cq, hpq]
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hep, Nat.mod_eq_of_lt heq] at hc
    have hr : rAt RP p = rAt RP q := vAt_inj hInc rp rq (by rw [← vp, ← vq, hc])
    rw [← ip, ← iq, hr]
  unfold shortValsOK
  apply distinctCheck_of_injective
  intro p q hp hq h
  rw [shortValsN_size'] at hp hq
  rw [shortValsN_get' _ p hp, shortValsN_get' _ q hq] at h
  exact hinj p q hp hq h

end CFSG.KC.ShortVals
