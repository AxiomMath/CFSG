module

public import Certificates.Data.Kernel.D4PlaneP
import CFSG.Certificates.Kernel.D42KSound

public section

namespace CFSG.KC.D4PlaneP

open CFSG.Quasithin CFSG.AGLEmbedding.D4Two

def rN : Nat → Nat
  | 0 => 0
  | N + 1 => 2 ^ 8 * rN N + 1

theorem r3_eq : r3 = rN 24 := by decide +kernel

theorem land_step (x R : Nat) : x &&& (2 ^ 8 * R + 1) = 2 ^ 8 * ((x >>> 8) &&& R) + (x &&& 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  have h1 : (1 : Nat) < 2 ^ 8 := by decide
  have h2 : x &&& 1 < 2 ^ 8 := Nat.lt_of_le_of_lt Nat.and_le_right h1
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ h1, Nat.testBit_two_pow_mul_add _ h2]
  by_cases hj : j < 8
  · simp only [hj, ↓reduceIte, Nat.testBit_and]
  · simp only [hj, ↓reduceIte, Nat.testBit_and, Nat.testBit_shiftRight]
    rw [Nat.add_sub_cancel' (by omega)]

theorem testBit_spread (N : Nat) : ∀ (x m : Nat),
    ((x &&& rN N) * 255).testBit m = (decide (m < 8 * N) && x.testBit (m - m % 8)) := by
  induction N with
  | zero => intro x m; simp [rN]
  | succ N ih =>
    intro x m
    have hb : (x &&& 1) * 255 < 2 ^ 8 := by
      have := @Nat.and_le_right x 1
      have : (x &&& 1) * 255 ≤ 1 * 255 := Nat.mul_le_mul_right _ this
      omega
    rw [rN, land_step, Nat.add_mul, Nat.mul_assoc, Nat.testBit_two_pow_mul_add _ hb]
    by_cases hm : m < 8
    · simp only [hm, ↓reduceIte]
      have e1 : m - m % 8 = 0 := by omega
      rw [e1, decide_eq_true (by omega : m < 8 * (N + 1)), Bool.true_and, Nat.and_one_is_mod]
      rcases Nat.mod_two_eq_zero_or_one x with h | h
      · rw [h, Nat.testBit_zero, h]
        simp
      · rw [h, Nat.testBit_zero, h]
        interval_cases m <;> decide
    · simp only [hm, ↓reduceIte]
      rw [ih, Nat.testBit_shiftRight]
      have e1 : 8 + (m - 8 - (m - 8) % 8) = m - m % 8 := by omega
      rw [e1]
      congr 1
      simp only [decide_eq_decide]
      omega

theorem testBit_rowSpread (y : Nat) (hy : y < 2 ^ 8) (N : Nat) : ∀ m : Nat,
    (y * rN N).testBit m = (decide (m < 8 * N) && y.testBit (m % 8)) := by
  induction N with
  | zero => intro m; simp [rN]
  | succ N ih =>
    intro m
    have e : y * rN (N + 1) = 2 ^ 8 * (y * rN N) + y := by
      rw [rN]
      ring
    rw [e, Nat.testBit_two_pow_mul_add _ hy]
    by_cases hm : m < 8
    · simp only [hm, ↓reduceIte]
      rw [decide_eq_true (by omega : m < 8 * (N + 1)), Bool.true_and, Nat.mod_eq_of_lt hm]
    · simp only [hm, ↓reduceIte]
      rw [ih]
      have e1 : (m - 8) % 8 = m % 8 := by omega
      rw [e1]
      congr 1
      simp only [decide_eq_decide]
      omega

theorem testBit_laneK (X Y k o m : Nat) :
    (laneK (((X >>> k) &&& r3) * 255) Y o).testBit m =
      (decide (m < 192) && X.testBit (k + (m - m % 8)) && Y.testBit (o + m % 8)) := by
  have hy : (Y >>> o) &&& 255 < 2 ^ 8 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have e255 : (255 : Nat) = 2 ^ 8 - 1 := rfl
  have h255 : (255 : Nat).testBit (m % 8) = true := by
    rw [e255, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true (Nat.mod_lt _ (by decide))
  have e192 : (8 * 24 : Nat) = 192 := rfl
  rw [laneK, Nat.testBit_and, r3_eq, testBit_spread, testBit_rowSpread _ hy, Nat.testBit_and,
    Nat.testBit_shiftRight, Nat.testBit_shiftRight, h255, e192]
  by_cases hm : m < 192 <;> simp [hm]

theorem testBit_laneK_pos (X Y k o q L : Nat) (hq : q < 64) :
    (laneK (((X >>> k) &&& r3) * 255) Y o).testBit (q + 64 * L) =
      (decide (L < 3) && X.testBit (k + (q - q % 8 + 64 * L)) && Y.testBit (o + q % 8)) := by
  have e1 : (q + 64 * L) % 8 = q % 8 := by omega
  have e2 : q + 64 * L - q % 8 = q - q % 8 + 64 * L := by omega
  have e3 : decide (q + 64 * L < 192) = decide (L < 3) := by
    simp only [decide_eq_decide]
    omega
  rw [testBit_laneK, e1, e2, e3]

theorem testBit_shl64 (z q L : Nat) (hq : q < 64) :
    (z <<< 64).testBit (q + 64 * L) = (decide (1 ≤ L) && z.testBit (q + 64 * (L - 1))) := by
  rw [Nat.testBit_shiftLeft]
  by_cases h : 1 ≤ L
  · have e : q + 64 * L - 64 = q + 64 * (L - 1) := by omega
    rw [e, decide_eq_true h, decide_eq_true (by omega)]
  · rw [decide_eq_false h, decide_eq_false (by omega)]
    simp

theorem testBit_shl128 (z q L : Nat) (hq : q < 64) :
    (z <<< 128).testBit (q + 64 * L) = (decide (2 ≤ L) && z.testBit (q + 64 * (L - 2))) := by
  rw [Nat.testBit_shiftLeft]
  by_cases h : 2 ≤ L
  · have e : q + 64 * L - 128 = q + 64 * (L - 2) := by omega
    rw [e, decide_eq_true h, decide_eq_true (by omega)]
  · rw [decide_eq_false h, decide_eq_false (by omega)]
    simp

theorem testBit_mulK_pos (X Y k q L : Nat) (hq : q < 64) :
    (mulK X Y k).testBit (q + 64 * L) =
      (((decide (L < 3) && X.testBit (k + (q - q % 8 + 64 * L)) && Y.testBit (8 * k + q % 8)) ^^
        (decide (1 ≤ L) && (decide (L - 1 < 3) && X.testBit (k + (q - q % 8 + 64 * (L - 1))) &&
          Y.testBit (64 + 8 * k + q % 8)))) ^^
        (decide (2 ≤ L) && (decide (L - 2 < 3) && X.testBit (k + (q - q % 8 + 64 * (L - 2))) &&
          Y.testBit (128 + 8 * k + q % 8)))) := by
  rw [mulK, mulKs, Nat.testBit_xor, Nat.testBit_xor, testBit_shl64 _ _ _ hq, testBit_shl128 _ _ _ hq,
    testBit_laneK_pos _ _ _ _ _ _ hq, testBit_laneK_pos _ _ _ _ _ _ hq,
    testBit_laneK_pos _ _ _ _ _ _ hq]

theorem testBit_mulK_hi (X Y k m : Nat) (hm : 320 ≤ m) : (mulK X Y k).testBit m = false := by
  rw [mulK, mulKs, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft,
    testBit_laneK, testBit_laneK, testBit_laneK]
  have h1 : ¬ m < 192 := by omega
  have h2 : ¬ m - 64 < 192 := by omega
  have h3 : ¬ m - 128 < 192 := by omega
  simp [h1, h2, h3]

theorem testBit_m64 (n : Nat) : m64.testBit n = decide (n < 64) := by
  have e : m64 = 2 ^ 64 - 1 := rfl
  rw [e]
  exact Nat.testBit_two_pow_sub_one 64 n

theorem testBit_m192 (n : Nat) : m192.testBit n = decide (n < 192) := by
  have e : m192 = 2 ^ 192 - 1 := rfl
  rw [e]
  exact Nat.testBit_two_pow_sub_one 192 n

theorem testBit_redP (x n : Nat) :
    (redP x).testBit n =
      (((((x.testBit n && decide (n < 192)) ^^ (x.testBit (192 + n) && decide (n < 64))) ^^
        (decide (64 ≤ n) && (x.testBit (192 + (n - 64)) && decide (n - 64 < 64)))) ^^
        (decide (64 ≤ n) && x.testBit (256 + (n - 64)))) ^^
        (decide (128 ≤ n) && x.testBit (256 + (n - 128)))) := by
  simp only [redP, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftLeft,
    testBit_m64, testBit_m192, ge_iff_le]

theorem testBit_redP0 (x q : Nat) (hq : q < 64) :
    (redP x).testBit (q + 64 * 0) = (x.testBit (q + 64 * 0) ^^ x.testBit (q + 64 * 3)) := by
  have i0 : q + 64 * 0 = q := by omega
  have i1 : q + 64 * 3 = 192 + q := by omega
  rw [i0, i1, testBit_redP, decide_eq_true (by omega : q < 192), decide_eq_true hq,
    decide_eq_false (by omega : ¬ 64 ≤ q), decide_eq_false (by omega : ¬ 128 ≤ q)]
  simp only [Bool.and_true, Bool.false_and, Bool.xor_false]

theorem testBit_redP1 (x q : Nat) (hq : q < 64) :
    (redP x).testBit (q + 64 * 1) =
      ((x.testBit (q + 64 * 1) ^^ x.testBit (q + 64 * 3)) ^^ x.testBit (q + 64 * 4)) := by
  have i0 : q + 64 * 1 - 64 = q := by omega
  have i1 : q + 64 * 3 = 192 + q := by omega
  have i2 : q + 64 * 4 = 256 + q := by omega
  rw [testBit_redP, i0, i1, i2, decide_eq_true (by omega : q + 64 * 1 < 192),
    decide_eq_false (by omega : ¬ q + 64 * 1 < 64), decide_eq_true (by omega : 64 ≤ q + 64 * 1),
    decide_eq_true hq, decide_eq_false (by omega : ¬ 128 ≤ q + 64 * 1)]
  simp only [Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and, Bool.xor_false]

theorem testBit_redP2 (x q : Nat) (hq : q < 64) (hx : ∀ m, 320 ≤ m → x.testBit m = false) :
    (redP x).testBit (q + 64 * 2) = (x.testBit (q + 64 * 2) ^^ x.testBit (q + 64 * 4)) := by
  have i0 : q + 64 * 2 - 128 = q := by omega
  have i2 : q + 64 * 4 = 256 + q := by omega
  rw [testBit_redP, i0, i2, hx (256 + (q + 64 * 2 - 64)) (by omega),
    decide_eq_true (by omega : q + 64 * 2 < 192), decide_eq_false (by omega : ¬ q + 64 * 2 < 64),
    decide_eq_false (by omega : ¬ q + 64 * 2 - 64 < 64), decide_eq_true (by omega : 64 ≤ q + 64 * 2),
    decide_eq_true (by omega : 128 ≤ q + 64 * 2)]
  simp only [Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and, Bool.xor_false]

theorem testBit_redP_hi (x n : Nat) (hn : 192 ≤ n) (hx : ∀ m, 320 ≤ m → x.testBit m = false) :
    (redP x).testBit n = false := by
  rw [testBit_redP, hx (256 + (n - 64)) (by omega), hx (256 + (n - 128)) (by omega),
    decide_eq_false (by omega : ¬ n < 192), decide_eq_false (by omega : ¬ n < 64),
    decide_eq_false (by omega : ¬ n - 64 < 64)]
  simp only [Bool.and_false, Bool.xor_false]

theorem redF_xor (d1 d2 d3 d4 d5 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 : Bool) :
    (((((((a1 ^^ b1) && d1) ^^ ((a2 ^^ b2) && d2)) ^^ (d3 && ((a3 ^^ b3) && d4))) ^^
      (d3 && (a4 ^^ b4))) ^^ (d5 && (a5 ^^ b5))) =
      (((((((a1 && d1) ^^ (a2 && d2)) ^^ (d3 && (a3 && d4))) ^^ (d3 && a4)) ^^ (d5 && a5)) ^^
        (((((b1 && d1) ^^ (b2 && d2)) ^^ (d3 && (b3 && d4))) ^^ (d3 && b4)) ^^ (d5 && b5))))) := by
  revert d1 d2 d3 d4 d5 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5
  decide +kernel

theorem redP_xor (u v : Nat) : redP (u ^^^ v) = redP u ^^^ redP v := by
  apply Nat.eq_of_testBit_eq
  intro n
  rw [Nat.testBit_xor, testBit_redP, testBit_redP, testBit_redP]
  simp only [Nat.testBit_xor]
  exact redF_xor _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem toNat_lt (e : GF8) : e.toNat < 8 := e.val.isLt

theorem testBit_toNat_hi (e : GF8) (i : Nat) (hi : 3 ≤ i) : e.toNat.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (toNat_lt e)
    (Nat.pow_le_pow_right (by decide) hi : 2 ^ 3 ≤ 2 ^ i))

theorem testBit_encE (v : Nat) (hv : v < 8) (n : Nat) :
    (encE v).testBit n = (decide (n % 64 = 0) && v.testBit (n / 64)) := by
  by_cases hn : n < 256
  · have key : ∀ v < 8, ∀ n < 256,
        (encE v).testBit n = (decide (n % 64 = 0) && v.testBit (n / 64)) := by decide +kernel
    exact key v hv n hn
  · have hb : ∀ v < 8, encE v < 2 ^ 256 := by decide +kernel
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hb v hv)
      (Nat.pow_le_pow_right (by decide) (by omega)))]
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv
      (Nat.pow_le_pow_right (by decide) (by omega) : 2 ^ 3 ≤ 2 ^ (n / 64)))]
    simp

theorem toNat_zero : (0 : GF8).toNat = 0 := rfl

theorem testBit_packL : ∀ (l : List GF8), l.length ≤ 64 → ∀ n : Nat,
    (packL l).testBit n = (l.getD (n % 64) 0).toNat.testBit (n / 64)
  | [], _, n => by simp [packL, toNat_zero]
  | e :: l, hl, n => by
    have hl' : l.length ≤ 63 := by simp at hl; omega
    have ih := testBit_packL l (by omega)
    rw [packL, Nat.testBit_or, testBit_encE _ (toNat_lt e), Nat.testBit_shiftLeft]
    by_cases h : n % 64 = 0
    · rw [h, List.getD_cons_zero, decide_eq_true rfl, Bool.true_and]
      by_cases h0 : n = 0
      · subst h0
        simp
      · rw [ih, decide_eq_true (by omega : n ≥ 1)]
        have e : (n - 1) % 64 = 63 := by omega
        rw [e, List.getD_eq_default _ _ (by omega), toNat_zero, Nat.zero_testBit]
        simp
    · rw [decide_eq_false h, Bool.false_and, Bool.false_or, ih, decide_eq_true (by omega : n ≥ 1)]
      have e1 : (n - 1) % 64 = n % 64 - 1 := by omega
      have e2 : (n - 1) / 64 = n / 64 := by omega
      have e3 : n % 64 = n % 64 - 1 + 1 := by omega
      rw [e1, e2, Bool.true_and]
      conv_rhs => rw [e3, List.getD_cons_succ]

theorem testBit_packA (A : Array GF8) (n : Nat) :
    (packA A).testBit n = (A.getD (n % 64) 0).toNat.testBit (n / 64) := by
  rw [packA, testBit_packL _ (by simp)]
  have h : n % 64 < 64 := Nat.mod_lt _ (by decide)
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, h]

theorem packA_x (A : Array GF8) (k r L : Nat) (hk : k < 8) (hr : r < 8) :
    (packA A).testBit (k + (8 * r + 64 * L)) = (A.getD (8 * r + k) 0).toNat.testBit L := by
  have e1 : (k + (8 * r + 64 * L)) % 64 = 8 * r + k := by omega
  have e2 : (k + (8 * r + 64 * L)) / 64 = L := by omega
  rw [testBit_packA, e1, e2]

theorem packA_y0 (B : Array GF8) (k c : Nat) (hk : k < 8) (hc : c < 8) :
    (packA B).testBit (8 * k + c) = (B.getD (8 * k + c) 0).toNat.testBit 0 := by
  have e1 : (8 * k + c) % 64 = 8 * k + c := by omega
  have e2 : (8 * k + c) / 64 = 0 := by omega
  rw [testBit_packA, e1, e2]

theorem packA_y1 (B : Array GF8) (k c : Nat) (hk : k < 8) (hc : c < 8) :
    (packA B).testBit (64 + 8 * k + c) = (B.getD (8 * k + c) 0).toNat.testBit 1 := by
  have e1 : (64 + 8 * k + c) % 64 = 8 * k + c := by omega
  have e2 : (64 + 8 * k + c) / 64 = 1 := by omega
  rw [testBit_packA, e1, e2]

theorem packA_y2 (B : Array GF8) (k c : Nat) (hk : k < 8) (hc : c < 8) :
    (packA B).testBit (128 + 8 * k + c) = (B.getD (8 * k + c) 0).toNat.testBit 2 := by
  have e1 : (128 + 8 * k + c) % 64 = 8 * k + c := by omega
  have e2 : (128 + 8 * k + c) / 64 = 2 := by omega
  rw [testBit_packA, e1, e2]

theorem testBit_redK (A B : Array GF8) (k r c a : Nat) (hk : k < 8) (hr : r < 8) (hc : c < 8)
    (ha : a < 3) :
    (redP (mulK (packA A) (packA B) k)).testBit (8 * r + c + 64 * a) =
      (A.getD (8 * r + k) 0 * B.getD (8 * k + c) 0).toNat.testBit a := by
  have hq : 8 * r + c < 64 := by omega
  have hq8 : (8 * r + c) % 8 = c := by omega
  have hq8' : 8 * r + c - c = 8 * r := by omega
  interval_cases a
  all_goals first
    | rw [testBit_redP0 _ _ hq, testBit_mulK_pos _ _ _ _ 0 hq, testBit_mulK_pos _ _ _ _ 3 hq]
    | rw [testBit_redP1 _ _ hq, testBit_mulK_pos _ _ _ _ 1 hq, testBit_mulK_pos _ _ _ _ 3 hq,
        testBit_mulK_pos _ _ _ _ 4 hq]
    | rw [testBit_redP2 _ _ hq (testBit_mulK_hi _ _ _), testBit_mulK_pos _ _ _ _ 2 hq,
        testBit_mulK_pos _ _ _ _ 4 hq]
  all_goals
    rw [hq8, hq8']
    repeat rw [packA_x A k r _ hk hr]
    rw [packA_y0 B k c hk hc, packA_y1 B k c hk hc, packA_y2 B k c hk hc]
    generalize A.getD (8 * r + k) 0 = x
    generalize B.getD (8 * k + c) 0 = y
    revert x y
    decide

theorem testBit_mulP (X Y n : Nat) :
    (mulP X Y).testBit n =
      ((redP (mulK X Y 0)).testBit n ^^ (redP (mulK X Y 1)).testBit n ^^
        (redP (mulK X Y 2)).testBit n ^^ (redP (mulK X Y 3)).testBit n ^^
        (redP (mulK X Y 4)).testBit n ^^ (redP (mulK X Y 5)).testBit n ^^
        (redP (mulK X Y 6)).testBit n ^^ (redP (mulK X Y 7)).testBit n) := by
  simp only [mulP, redP_xor, Nat.testBit_xor]

theorem packA_mulArr (A B : Array GF8) : packA (mulArr A B) = mulP (packA A) (packA B) := by
  apply Nat.eq_of_testBit_eq
  intro n
  rw [testBit_mulP]
  by_cases hn : n < 192
  · obtain ⟨r, c, a, hr, hc, ha, rfl⟩ : ∃ r c a, r < 8 ∧ c < 8 ∧ a < 3 ∧ n = 8 * r + c + 64 * a :=
      ⟨n % 64 / 8, n % 8, n / 64, by omega, by omega, by omega, by omega⟩
    rw [testBit_redK A B 0 r c a (by omega) hr hc ha, testBit_redK A B 1 r c a (by omega) hr hc ha,
      testBit_redK A B 2 r c a (by omega) hr hc ha, testBit_redK A B 3 r c a (by omega) hr hc ha,
      testBit_redK A B 4 r c a (by omega) hr hc ha, testBit_redK A B 5 r c a (by omega) hr hc ha,
      testBit_redK A B 6 r c a (by omega) hr hc ha, testBit_redK A B 7 r c a (by omega) hr hc ha]
    have e1 : (8 * r + c + 64 * a) % 64 = 8 * r + c := by omega
    have e2 : (8 * r + c + 64 * a) / 64 = a := by omega
    rw [testBit_packA, e1, e2, CFSG.KC.D42K.getD_mulArr A B hr hc]
    simp only [CFSG.KC.D42K.toNat_add, Nat.testBit_xor]
  · have hx : ∀ k m, 320 ≤ m → (mulK (packA A) (packA B) k).testBit m = false :=
      fun k m hm => testBit_mulK_hi _ _ k m hm
    have hz : ∀ k, (redP (mulK (packA A) (packA B) k)).testBit n = false :=
      fun k => testBit_redP_hi _ n (by omega) (hx k)
    rw [testBit_packA, testBit_toNat_hi _ _ (by omega)]
    simp only [hz, Bool.xor_false]

theorem packA_inj {A B : Array GF8} (hA : A.size = 64) (hB : B.size = 64)
    (h : packA A = packA B) : A = B := by
  refine Array.ext (by rw [hA, hB]) fun t h1 h2 => ?_
  have ht : t < 64 := hA ▸ h1
  have key : (A.getD t 0).toNat = (B.getD t 0).toNat := by
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 3
    · have e := congrArg (fun x => x.testBit (t + 64 * i)) h
      have e1 : (t + 64 * i) % 64 = t := by omega
      have e2 : (t + 64 * i) / 64 = i := by omega
      simp only [testBit_packA, e1, e2] at e
      exact e
    · rw [testBit_toNat_hi _ _ (by omega), testBit_toNat_hi _ _ (by omega)]
  have e2 := CFSG.KC.D42K.toNat_inj key
  rwa [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1,
    Array.getElem?_eq_getElem h2, Option.getD_some, Option.getD_some] at e2

theorem beq_pack {A B : Array GF8} (hA : A.size = 64) (hB : B.size = 64) :
    (A == B) = (packA A == packA B) := by
  apply Bool.eq_iff_iff.2
  rw [beq_iff_eq, beq_iff_eq]
  exact ⟨fun h => h ▸ rfl, packA_inj hA hB⟩

theorem packA_oneArr : packA oneArr = oneP := by decide +kernel

theorem all_congr_mem {α : Type} {l : List α} {p q : α → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons]
    rw [h a (by simp), ih fun x hx => h x (by simp [hx])]

theorem any_congr_mem {α : Type} {l : List α} {p q : α → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons]
    rw [h a (by simp), ih fun x hx => h x (by simp [hx])]

theorem contains_pack (l : List (Array GF8)) (y : Array GF8) (hl : ∀ a ∈ l, a.size = 64)
    (hy : y.size = 64) : (l.map packA).contains (packA y) = l.contains y := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.contains_cons]
    rw [ih fun x hx => hl x (by simp [hx]), beq_pack hy (hl a (by simp))]

theorem size_letterArr (l : Nat) : (letterArr l).size = 64 := size_ofMat _

theorem size_arrProd (l : List (Array GF8)) : (arrProd l).size = 64 := by
  cases l with
  | nil => exact size_oneArr
  | cons a l =>
    rw [arrProd, List.foldr_cons]
    exact size_mulArr _ _

theorem size_bfs (A B : Array GF8) (par : List (Nat × Bool)) :
    ∀ acc : List (Array GF8), (∀ x ∈ acc, x.size = 64) →
      ∀ x ∈ par.foldl (bfsStep A B) acc, x.size = 64 := by
  induction par with
  | nil => exact fun acc h => h
  | cons p par ih =>
    intro acc h
    refine ih _ fun x hx => ?_
    simp only [bfsStep, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact h x hx
    · exact size_mulArr _ _

theorem size_sylowElems : ∀ x ∈ sylowElems, x.size = 64 :=
  size_bfs _ _ _ _ fun x hx => by
    rw [List.mem_singleton] at hx
    rw [hx]
    exact size_oneArr

theorem size_sylowElemAt (i : Nat) : (sylowElemAt i).size = 64 := by
  unfold sylowElemAt
  rw [List.getD_eq_getElem?_getD]
  cases h : sylowElems[i]? with
  | none => exact size_oneArr
  | some x => exact size_sylowElems x (List.mem_of_getElem? h)

theorem getD_some {α : Type} {l : List α} {i : Nat} (d : α) (h : i < l.length) :
    l[i]? = some (l.getD i d) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem getD_take {α : Type} (l : List α) (m i : Nat) (d : α) (h : i < m) :
    (l.take m).getD i d = l.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos h]

theorem bfsP_of_bfsOK (A B : Nat) (par : List (Nat × Bool)) (es : List Nat)
    (h : bfsOK A B par es = true) : bfsP A B par = es := by
  unfold bfsOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hlen, h0⟩, hk⟩ := h
  have key : ∀ n, n ≤ par.length →
      (par.take n).foldl (bfsStepP A B) [oneP] = es.take (n + 1) := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [List.take_zero, List.foldl_nil, List.take_succ, List.take_zero, List.nil_append,
        getD_some 0 (by omega), h0]
      rfl
    | succ n ih =>
      intro hn
      have hkn := hk n (by omega)
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hkn
      obtain ⟨hp, he⟩ := hkn
      rw [List.take_succ, List.foldl_append, ih (by omega), getD_some (0, false) (by omega),
        Option.toList_some, List.foldl_cons, List.foldl_nil, bfsStepP,
        List.take_succ (l := es) (i := n + 1), getD_some 0 (by omega), Option.toList_some, he]
      congr 3
      exact getD_take _ _ _ _ (by omega)
  have e := key par.length le_rfl
  rw [List.take_length, List.take_of_length_le (by omega)] at e
  exact e

section Twin

variable {ls : List Nat} (hL : ∀ i < 18, packA (letterArr i) = ls.getD i 0)

include hL

theorem packA_letterArr (l : Nat) : packA (letterArr l) = letP ls l := by
  unfold letP
  by_cases hl : l < 18
  · rw [Nat.min_eq_left (by omega), hL l hl]
  · have h1 : ¬ l < 8 := by omega
    have h2 : ¬ l < 16 := by omega
    have h3 : ¬ l = 16 := by omega
    have e : letterArr l = letterArr 17 := by
      simp only [letterArr, letterMat, if_neg h1, if_neg h2, if_neg h3]
      rfl
    rw [e, Nat.min_eq_right (by omega), hL 17 (by decide)]

theorem packA_wordArr (w : List Nat) : packA (wordArr w) = wordP ls w := by
  induction w with
  | nil => exact packA_oneArr
  | cons l w ih =>
    rw [wordArr_cons, packA_mulArr, ih, packA_letterArr hL]
    rfl

omit hL in
theorem map_bfs (A B : Array GF8) (par : List (Nat × Bool)) :
    ∀ acc : List (Array GF8), (par.foldl (bfsStep A B) acc).map packA =
      par.foldl (bfsStepP (packA A) (packA B)) (acc.map packA) := by
  induction par with
  | nil => exact fun _ => rfl
  | cons p par ih =>
    intro acc
    rw [List.foldl_cons, List.foldl_cons, ih]
    congr 1
    simp only [bfsStep, bfsStepP, List.map_append, List.map_cons, List.map_nil, packA_mulArr]
    rw [← packA_oneArr, List.getD_map]
    cases p.2 <;> rfl

theorem map_sylowElems : sylowElems.map packA = enumP ls := by
  rw [sylowElems, bfsElems, map_bfs, enumP, bfsP, genA, genB, packA_wordArr hL,
    packA_wordArr hL]
  simp only [List.map_cons, List.map_nil, packA_oneArr]

omit hL in
theorem packA_sylowElemAt (i : Nat) :
    packA (sylowElemAt i) = atP (sylowElems.map packA) i := by
  rw [atP, ← packA_oneArr, List.getD_map]
  rfl

omit hL in
theorem map_planeSpan (x y : Array GF8) : (planeSpan x y).map packA =
    spanP (packA x) (packA y) := by
  simp only [planeSpan, spanP, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
    List.map_append, List.append_nil, packA_mulArr, packA_oneArr]

omit hL in
theorem size_planeSpan (x y : Array GF8) : ∀ p ∈ planeSpan x y, p.size = 64 := by
  intro p hp
  rw [planeSpan, List.mem_flatMap] at hp
  obtain ⟨u, -, hp⟩ := hp
  obtain ⟨v, -, rfl⟩ := List.mem_map.1 hp
  exact size_mulArr u v

omit hL in
theorem cover_eq (cs : List D4PlaneCert) :
    planeCoverCheck cs sylowElems = coverP (sylowElems.map packA) cs := by
  unfold planeCoverCheck coverP coverR
  dsimp only
  have hc : ∀ x ∈ sylowElems, cube1 x = (cube1P ∘ packA) x := by
    intro x hx
    simp only [cube1, cube1P, Function.comp, beq_pack (size_mulArr _ _) size_oneArr,
      packA_mulArr, packA_oneArr]
  have hOm : (sylowElems.map packA).filter cube1P = (sylowElems.filter cube1).map packA := by
    rw [List.filter_map, List.filter_congr hc]
  have hOmS : ∀ x ∈ sylowElems.filter cube1, x.size = 64 :=
    fun x hx => size_sylowElems x (List.mem_filter.1 hx).1
  have hEs : cs.map (fun c => c.idxs.map (atP (sylowElems.map packA))) =
      (cs.map D4PlaneCert.elems).map (List.map packA) := by
    rw [List.map_map]
    refine List.map_congr_left fun c _ => ?_
    rw [Function.comp_apply, D4PlaneCert.elems, List.map_map]
    exact List.map_congr_left fun i _ => (packA_sylowElemAt i).symm
  rw [hOm, hEs, List.all_map]
  refine all_congr_mem fun x hx => ?_
  simp only [Function.comp]
  rw [beq_pack (hOmS x hx) size_oneArr, packA_oneArr]
  refine congrArg (fun t => _ || t) ?_
  have hf : ∀ y ∈ sylowElems.filter cube1, commutes x y = (commP (packA x) ∘ packA) y := by
    intro y hy
    simp only [commutes, commP, Function.comp, beq_pack (size_mulArr _ _) (size_mulArr _ _),
      packA_mulArr]
  rw [List.filter_map, ← List.filter_congr hf, List.all_map]
  refine all_congr_mem fun y hy => ?_
  have hyS : y.size = 64 := hOmS y (List.mem_filter.1 hy).1
  simp only [Function.comp]
  have e3 : [oneP, packA x, mulP (packA x) (packA x)] = [oneArr, x, mulArr x x].map packA := by
    simp only [List.map_cons, List.map_nil, packA_oneArr, packA_mulArr]
  rw [e3, contains_pack _ _ (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with h | h | h
    · rw [h]
      exact size_oneArr
    · rw [h]
      exact hOmS x hx
    · rw [h]
      exact size_mulArr _ _) hyS]
  refine congrArg (fun t => _ || t) ?_
  rw [List.any_map (f := List.map packA)]
  refine any_congr_mem fun E hE => ?_
  have hES : ∀ p ∈ E, p.size = 64 := by
    intro p hp
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hE
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hp
    exact size_sylowElemAt i
  simp only [Function.comp]
  rw [contains_pack E x hES (hOmS x hx), contains_pack E y hES hyS, List.all_map, ← map_planeSpan]
  refine congrArg (fun t => _ && t) ?_
  refine all_congr_mem fun p hp => ?_
  simp only [Function.comp]
  rw [contains_pack _ _ (size_planeSpan x y) (hES p hp)]

theorem pool_eq (c : D4PlaneCert) : c.poolOK = poolP ls (sylowElems.map packA) c := by
  unfold D4PlaneCert.poolOK poolP
  refine all_congr_mem fun e _ => ?_
  simp only [commutes, commP, bne, beq_pack (size_mulArr _ _) (size_mulArr _ _),
    beq_pack (size_sylowElemAt _) size_oneArr, packA_mulArr, packA_oneArr, packA_sylowElemAt,
    packA_wordArr hL]

omit hL in
theorem packA_arrProd (l : List (Array GF8)) : packA (arrProd l) = prodP (l.map packA) := by
  induction l with
  | nil => exact packA_oneArr
  | cons a l ih =>
    rw [arrProd, List.foldr_cons, packA_mulArr]
    rw [arrProd] at ih
    rw [ih]
    rfl

theorem target_eq (c : D4PlaneCert) : c.targetOK = targetP ls c := by
  unfold D4PlaneCert.targetOK targetP
  dsimp only
  have hpa : c.pool.map (fun e => wordP ls e.1) = c.poolArr.map packA := by
    rw [D4PlaneCert.poolArr, List.map_map]
    exact List.map_congr_left fun e _ => (packA_wordArr hL e.1).symm
  have hf : (packA ∘ fun m => c.poolArr.getD m oneArr) =
      fun m => (c.poolArr.map packA).getD m oneP := by
    funext m
    rw [← packA_oneArr, List.getD_map]
    rfl
  rw [hpa]
  refine all_congr_mem fun j _ => ?_
  rw [beq_pack (size_arrProd _) (size_letterArr _), packA_arrProd, packA_letterArr hL,
    List.map_map, hf]

theorem d4PlaneCheck_of {es : List Nat}
    (hE : bfsOK (wordP ls wordA) (wordP ls wordB) bfsPar es = true)
    (hC : coverP es d4PlaneCerts = true)
    (hP : d4PlaneCerts.all (fun c => poolP ls es c && targetP ls c) = true) :
    d4PlaneCheck = true := by
  have hS : sylowElems.map packA = es := (map_sylowElems hL).trans (bfsP_of_bfsOK _ _ _ _ hE)
  unfold d4PlaneCheck
  rw [Bool.and_eq_true, cover_eq, hS]
  refine ⟨hC, ?_⟩
  rw [← hP]
  refine all_congr_mem fun c _ => ?_
  rw [pool_eq hL, target_eq hL, hS]

end Twin

end CFSG.KC.D4PlaneP

end
