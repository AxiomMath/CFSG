module

public import Certificates.Data.Kernel.U62.Pair
public import CFSG.Certificates.Kernel.F4MatSound
import all CFSG.Fischer.F4
public import CFSG.Fischer.UnitaryPerm

public section

namespace CFSG.KC.U62P.Snd

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.F4M CFSG.KC.F4M.Aux CFSG.Fischer CFSG.F4.Native Matrix

theorem strictB_eq (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by cases y <;> rfl

theorem fget_eq (X i w : ℕ) : fget X i w = X >>> (i * w) % 2 ^ w := by
  change (X >>> (i * w)) &&& (1 <<< w - 1) = _
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod]

theorem testBit_fget (X i w n : ℕ) :
    (fget X i w).testBit n = (decide (n < w) && X.testBit (i * w + n)) := by
  rw [fget_eq, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

theorem testBit_omB_zero (m M : ℕ) : (omB m M).testBit 0 = (M.testBit 1 && m.testBit 0) := by
  unfold omB
  change ((M >>> 1 &&& m) ||| (((M &&& m) ^^^ (M >>> 1 &&& m)) <<< 1)).testBit 0 = _
  rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
  simp

theorem testBit_omB_succ (m M n : ℕ) :
    (omB m M).testBit (n + 1) = ((M.testBit (n + 2) && m.testBit (n + 1)) ||
      ((M.testBit n && m.testBit n) ^^ (M.testBit (n + 1) && m.testBit n))) := by
  unfold omB
  change ((M >>> 1 &&& m) ||| (((M &&& m) ^^^ (M >>> 1 &&& m)) <<< 1)).testBit (n + 1) = _
  rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftLeft, 
      Nat.testBit_xor, Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight]
  simp [Nat.add_comm 1]

theorem testBit_barB_zero (m M : ℕ) :
    (barB m M).testBit 0 = ((M.testBit 0 && m.testBit 0) ^^ (M.testBit 1 && m.testBit 0)) := by
  unfold barB
  change (((M &&& m) ^^^ (M >>> 1 &&& m)) ||| ((M >>> 1 &&& m) <<< 1)).testBit 0 = _
  rw [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
  simp [Nat.add_comm 1]

theorem testBit_barB_succ (m M n : ℕ) :
    (barB m M).testBit (n + 1) = (((M.testBit (n + 1) && m.testBit (n + 1)) ^^ (M.testBit (n + 2) && m.testBit (n + 1))) ||
      (M.testBit (n + 1) && m.testBit n)) := by
  unfold barB
  change (((M &&& m) ^^^ (M >>> 1 &&& m)) ||| ((M >>> 1 &&& m) <<< 1)).testBit (n + 1) = _
  rw [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_shiftRight]
  simp [Nat.add_comm 1]

theorem LO_testBit (n : ℕ) : LO.testBit n = (decide (n < 72) && decide (n % 2 = 0)) := by
  by_cases h : n < 72
  · interval_cases n <;> decide
  · rw [decide_eq_false h]
    simp only [Bool.false_and]
    apply Nat.testBit_lt_two_pow
    · exact lt_of_lt_of_le (by decide : LO < 2 ^ 72) (Nat.pow_le_pow_right (by decide) (by omega))

theorem LOV_testBit (n : ℕ) : LOV.testBit n = (decide (n < 12) && decide (n % 2 = 0)) := by
  by_cases h : n < 12
  · interval_cases n <;> decide
  · rw [decide_eq_false h]
    simp only [Bool.false_and]
    apply Nat.testBit_lt_two_pow
    · exact lt_of_lt_of_le (by decide : LOV < 2 ^ 12) (Nat.pow_le_pow_right (by decide) (by omega))

def IsMask (m K : ℕ) : Prop := ∀ n, m.testBit n = (decide (n < 2 * K) && decide (n % 2 = 0))

theorem mask_odd {m K : ℕ} (hm : IsMask m K) (j : ℕ) : m.testBit (2 * j + 1) = false := by
  rw [hm]
  have : (2 * j + 1) % 2 = 1 := by omega
  simp [this]

theorem mask_even {m K : ℕ} (hm : IsMask m K) (j : ℕ) : m.testBit (2 * j) = decide (j < K) := by
  rw [hm]
  have : (2 * j) % 2 = 0 := by omega
  simp [this]

theorem testBit_omB_even {m K : ℕ} (hm : IsMask m K) (M k : ℕ) :
    (omB m M).testBit (2 * k) = (decide (k < K) && M.testBit (2 * k + 1)) := by
  rcases k with _ | j
  · rw [Nat.mul_zero, testBit_omB_zero, mask_even hm 0]
    simp [Bool.and_comm]
  · have key := testBit_omB_succ m M (2 * j + 1)
    have e1 : 2 * j + 1 + 1 = 2 * (j + 1) := by omega
    have e2 : 2 * j + 1 + 2 = 2 * (j + 1) + 1 := by omega
    rw [e1, e2] at key
    rw [key, mask_odd hm j, mask_even hm (j + 1)]
    simp [Bool.and_comm]

theorem testBit_omB_odd {m K : ℕ} (hm : IsMask m K) (M k : ℕ) :
    (omB m M).testBit (2 * k + 1) =
      (decide (k < K) && (M.testBit (2 * k) ^^ M.testBit (2 * k + 1))) := by
  have key := testBit_omB_succ m M (2 * k)
  have e2 : 2 * k + 2 = 2 * (k + 1) := by omega
  rw [e2] at key
  rw [key, mask_even hm k, mask_odd hm k]
  generalize decide (k < K) = a
  generalize M.testBit (2 * k) = b
  generalize M.testBit (2 * k + 1) = c
  generalize M.testBit (2 * (k + 1)) = d
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem testBit_barB_even {m K : ℕ} (hm : IsMask m K) (M k : ℕ) :
    (barB m M).testBit (2 * k) =
      (decide (k < K) && (M.testBit (2 * k) ^^ M.testBit (2 * k + 1))) := by
  rcases k with _ | j
  · rw [Nat.mul_zero, testBit_barB_zero, mask_even hm 0]
    simp only [Nat.zero_add]
    generalize M.testBit 0 = b
    generalize M.testBit 1 = c
    generalize decide (0 < K) = a
    cases a <;> cases b <;> cases c <;> rfl
  · have key := testBit_barB_succ m M (2 * j + 1)
    have e1 : 2 * j + 1 + 1 = 2 * (j + 1) := by omega
    have e2 : 2 * j + 1 + 2 = 2 * (j + 1) + 1 := by omega
    rw [e1, e2] at key
    rw [key, mask_odd hm j, mask_even hm (j + 1)]
    generalize decide (j + 1 < K) = a
    generalize M.testBit (2 * (j + 1)) = b
    generalize M.testBit (2 * (j + 1) + 1) = c
    cases a <;> cases b <;> cases c <;> rfl

theorem testBit_barB_odd {m K : ℕ} (hm : IsMask m K) (M k : ℕ) :
    (barB m M).testBit (2 * k + 1) = (decide (k < K) && M.testBit (2 * k + 1)) := by
  have key := testBit_barB_succ m M (2 * k)
  have e2 : 2 * k + 2 = 2 * (k + 1) := by omega
  rw [e2] at key
  rw [key, mask_even hm k, mask_odd hm k]
  generalize decide (k < K) = a
  generalize M.testBit (2 * k + 1) = c
  generalize M.testBit (2 * (k + 1)) = d
  cases a <;> cases c <;> cases d <;> rfl

theorem fm2_eq : ∀ c < 4, fm 2 c = (if c.testBit 1 then 1 else 0) +
    2 * (if (c.testBit 0 ^^ c.testBit 1) then 1 else 0) := by decide

theorem sqC_eq : ∀ c < 4, fm c c = (if (c.testBit 0 ^^ c.testBit 1) then 1 else 0) +
    2 * (if c.testBit 1 then 1 else 0) := by decide

theorem testBit_fget2_zero (X k : ℕ) : (fget X k 2).testBit 0 = X.testBit (2 * k) := by
  rw [testBit_fget2]; simp

theorem testBit_fget2_one (X k : ℕ) : (fget X k 2).testBit 1 = X.testBit (2 * k + 1) := by
  rw [testBit_fget2]; simp

theorem four_le_pow (n : ℕ) : 4 ≤ 2 ^ (n + 2) := by
  have : 2 ^ 2 ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  simpa using this

theorem eq_of_bits {a b : ℕ} (ha : a < 4) (hb : b < 4) (h0 : a.testBit 0 = b.testBit 0)
    (h1 : a.testBit 1 = b.testBit 1) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro n
  rcases n with _ | _ | n
  · exact h0
  · exact h1
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (four_le_pow n)),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (four_le_pow n))]

theorem fget_omB {m K : ℕ} (hm : IsMask m K) (M k : ℕ) :
    fget (omB m M) k 2 = if k < K then fm 2 (fget M k 2) else 0 := by
  have hc : fget M k 2 < 4 := fget2_lt M k
  have h0 := testBit_fget2_zero M k
  have h1 := testBit_fget2_one M k
  have hl : fget (omB m M) k 2 < 4 := fget2_lt _ _
  split_ifs with hk
  · apply eq_of_bits hl (fm_lt _ _)
    · rw [testBit_fget2_zero, testBit_omB_even hm, fm2_eq _ hc, ← h1, decide_eq_true hk]
      generalize (fget M k 2).testBit 0 = b0
      generalize (fget M k 2).testBit 1 = b1
      cases b0 <;> cases b1 <;> decide
    · rw [testBit_fget2_one, testBit_omB_odd hm, fm2_eq _ hc, ← h0, ← h1, decide_eq_true hk]
      generalize (fget M k 2).testBit 0 = b0
      generalize (fget M k 2).testBit 1 = b1
      cases b0 <;> cases b1 <;> decide
  · apply eq_of_bits hl (by decide)
    · rw [testBit_fget2_zero, testBit_omB_even hm, decide_eq_false hk]
      rfl
    · rw [testBit_fget2_one, testBit_omB_odd hm, decide_eq_false hk]
      rfl

theorem fget_barB {m K : ℕ} (hm : IsMask m K) (M k : ℕ) :
    fget (barB m M) k 2 = if k < K then sqC (fget M k 2) else 0 := by
  have hc : fget M k 2 < 4 := fget2_lt M k
  have h0 := testBit_fget2_zero M k
  have h1 := testBit_fget2_one M k
  have hl : fget (barB m M) k 2 < 4 := fget2_lt _ _
  split_ifs with hk
  · apply eq_of_bits hl (fm_lt _ _)
    · rw [testBit_fget2_zero, testBit_barB_even hm, sqC_eq _ hc, ← h0, ← h1, decide_eq_true hk]
      generalize (fget M k 2).testBit 0 = b0
      generalize (fget M k 2).testBit 1 = b1
      cases b0 <;> cases b1 <;> decide
    · rw [testBit_fget2_one, testBit_barB_odd hm, sqC_eq _ hc, ← h1, decide_eq_true hk]
      generalize (fget M k 2).testBit 0 = b0
      generalize (fget M k 2).testBit 1 = b1
      cases b0 <;> cases b1 <;> decide
  · apply eq_of_bits hl (by decide)
    · rw [testBit_fget2_zero, testBit_barB_even hm, decide_eq_false hk]
      rfl
    · rw [testBit_fget2_one, testBit_barB_odd hm, decide_eq_false hk]
      rfl

theorem isMask_LO : IsMask LO 36 := by
  intro n
  rw [LO_testBit]

theorem isMask_LOV : IsMask LOV 6 := by
  intro n
  rw [LOV_testBit]

theorem fget2_xor (P Q k : ℕ) : fget (Nat.xor P Q) k 2 = Nat.xor (fget P k 2) (fget Q k 2) := by
  apply Nat.eq_of_testBit_eq
  intro n
  change (fget (P ^^^ Q) k 2).testBit n = ((fget P k 2) ^^^ (fget Q k 2)).testBit n
  rw [testBit_fget2, Nat.testBit_xor, Nat.testBit_xor, testBit_fget2, testBit_fget2]
  cases decide (n < 2) <;> rfl

theorem xorN_succ (n : ℕ) (f : ℕ → ℕ) : xorN (n + 1) f = Nat.xor (f n) (xorN n f) := rfl

theorem fget2_xorN (f : ℕ → ℕ) (j : ℕ) : ∀ n, fget (xorN n f) j 2 = xorN n (fun k => fget (f k) j 2)
  | 0 => by
    change fget 0 j 2 = 0
    simp [fget]
  | n + 1 => by
    rw [xorN_succ, xorN_succ, fget2_xor, fget2_xorN f j n]

theorem fget2_nIf (c : Bool) (x j : ℕ) : fget (nIf(c, x, 0)) j 2 = nIf(c, fget x j 2, 0) := by
  cases c
  · simp [fget]
  · rfl

theorem bit_eq (X i : ℕ) : bit X i = X.testBit i := by
  have h1 : (X >>> i) &&& 1 = X / 2 ^ i % 2 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.and_two_pow_sub_one_eq_mod _ 1
  change Nat.beq ((X >>> i) &&& 1) 1 = _
  rw [h1, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (X / 2 ^ i) with h | h <;> rw [h] <;> rfl

theorem fget_fget12 (P i j : ℕ) (hj : j < 6) : fget (fget P i 12) j 2 = fget P (6 * i + j) 2 := by
  apply Nat.eq_of_testBit_eq
  intro n
  rw [testBit_fget2, testBit_fget, testBit_fget2]
  by_cases hn : n < 2
  · have : 2 * j + n < 12 := by omega
    simp only [hn, this, decide_true, Bool.true_and]
    congr 1
    omega
  · simp [hn]

theorem orN_succ (n : ℕ) (f : ℕ → ℕ) : orN (n + 1) f = Nat.lor (f n) (orN n f) := rfl

theorem xorN_lt {w : ℕ} {f : ℕ → ℕ} (h : ∀ k, f k < 2 ^ w) : ∀ n, xorN n f < 2 ^ w
  | 0 => Nat.two_pow_pos w
  | n + 1 => by
    rw [xorN_succ]
    exact Nat.xor_lt_two_pow (h n) (xorN_lt h n)

theorem shiftLeft_lt {w : ℕ} {c : ℕ} (h : c < 2 ^ w) (n : ℕ) : Nat.shiftLeft c (Nat.mul w n) < 2 ^ (w * (n + 1)) := by
  change c <<< (w * n) < _
  rw [Nat.shiftLeft_eq, show w * (n + 1) = w + w * n by ring, pow_add]
  exact Nat.mul_lt_mul_of_pos_right h (by positivity)

theorem orN_lt {w : ℕ} {c : ℕ → ℕ} (h : ∀ k, c k < 2 ^ w) :
    ∀ n, orN n (fun t => Nat.shiftLeft (c t) (Nat.mul w t)) < 2 ^ (w * n)
  | 0 => by
    change 0 < 2 ^ (w * 0)
    simp
  | n + 1 => by
    rw [orN_succ]
    have h1 := shiftLeft_lt (h n) n
    have h2 : orN n (fun t => Nat.shiftLeft (c t) (Nat.mul w t)) < 2 ^ (w * (n + 1)) :=
      lt_of_lt_of_le (orN_lt h n) (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
    exact Nat.or_lt_two_pow h1 h2

theorem fget_shift {w c : ℕ} (hc : c < 2 ^ w) (n t : ℕ) :
    fget (Nat.shiftLeft c (Nat.mul w n)) t w = if t = n then c else 0 := by
  apply Nat.eq_of_testBit_eq
  intro b
  change (fget (c <<< (w * n)) t w).testBit b = _
  rw [testBit_fget, Nat.testBit_shiftLeft]
  by_cases hb : b < w
  · rcases lt_trichotomy t n with htn | rfl | htn
    · have : w * t + b < w * n := by nlinarith
      have h2 : ¬ (t * w + b ≥ w * n) := by rw [Nat.mul_comm t w]; omega
      simp [hb, h2, Nat.ne_of_lt htn]
    · simp [hb, Nat.mul_comm t w]
    · have h1 : w * n + w ≤ w * t := by nlinarith
      have h2 : t * w + b ≥ w * n := by rw [Nat.mul_comm t w]; omega
      have h3 : ¬ (t = n) := by omega
      have h4 : c.testBit (t * w + b - w * n) = false := by
        apply Nat.testBit_lt_two_pow
        exact lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) (by rw [Nat.mul_comm t w]; omega))
      simp [hb, h2, h3, h4]
  · have h4 : (if t = n then c else 0).testBit b = false := by
      apply Nat.testBit_lt_two_pow
      split_ifs
      · exact lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) (by omega))
      · exact Nat.two_pow_pos b
    rw [h4]
    simp [hb]

theorem fget_lor {w : ℕ} (a b t : ℕ) : fget (Nat.lor a b) t w = Nat.lor (fget a t w) (fget b t w) := by
  apply Nat.eq_of_testBit_eq
  intro n
  change (fget (a ||| b) t w).testBit n = ((fget a t w) ||| (fget b t w)).testBit n
  rw [testBit_fget, Nat.testBit_or, Nat.testBit_or, testBit_fget, testBit_fget]
  cases decide (n < w) <;> simp

theorem fget_orN {w : ℕ} {c : ℕ → ℕ} (h : ∀ k, c k < 2 ^ w) (n t : ℕ) :
    fget (orN n (fun t => Nat.shiftLeft (c t) (Nat.mul w t))) t w = if t < n then c t else 0 := by
  induction n with
  | zero =>
    change fget 0 t w = _
    simp [fget]
  | succ n ih =>
    rw [orN_succ, fget_lor, ih, fget_shift (h n) n t]
    by_cases htn : t = n
    · subst htn
      simp
    · by_cases ht : t < n
      · simp [htn, ht, show t < n + 1 by omega]
      · simp [htn, ht, show ¬ t < n + 1 by omega]

theorem omB_lt {m K : ℕ} (hm : IsMask m K) (M : ℕ) : omB m M < 2 ^ (2 * K) := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' i
  · rw [testBit_omB_even hm, decide_eq_false (by omega)]
    rfl
  · rw [testBit_omB_odd hm, decide_eq_false (by omega)]
    rfl

theorem barB_lt {m K : ℕ} (hm : IsMask m K) (M : ℕ) : barB m M < 2 ^ (2 * K) := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' i
  · rw [testBit_barB_even hm, decide_eq_false (by omega)]
    rfl
  · rw [testBit_barB_odd hm, decide_eq_false (by omega)]
    rfl

theorem omK_lt (M : ℕ) : omK M < 2 ^ 72 := omB_lt isMask_LO M

theorem omV_lt (v : ℕ) : omV v < 2 ^ 12 := omB_lt isMask_LOV v

theorem barV_lt (v : ℕ) : barV v < 2 ^ 12 := barB_lt isMask_LOV v

theorem ent_omK (M i j : ℕ) (hi : i < 6) (hj : j < 6) : ent (omK M) i j = fm 2 (ent M i j) := by
  change fget (omB LO M) (6 * i + j) 2 = fm 2 (fget M (6 * i + j) 2)
  rw [fget_omB isMask_LO, if_pos (by omega)]

theorem ent_barK (M i j : ℕ) (hi : i < 6) (hj : j < 6) : ent (barK M) i j = sqC (ent M i j) := by
  change fget (barB LO M) (6 * i + j) 2 = sqC (fget M (6 * i + j) 2)
  rw [fget_barB isMask_LO, if_pos (by omega)]

theorem decM_omK (M : ℕ) : decM (omK M) = (F4.ω : F4) • decM M := by
  ext i j
  rw [← cF4_ent, ent_omK M i j i.2 j.2, fm_spec (by norm_num) (ent_lt _ _ _), Matrix.smul_apply,
    ← cF4_ent, smul_eq_mul]
  rfl

theorem decM_barK (M : ℕ) : decM (barK M) = (decM M).map fun a => a ^ 2 := by
  ext i j
  rw [← cF4_ent, ent_barK M i j i.2 j.2, ← cF4_sq (ent_lt _ _ _), Matrix.map_apply, ← cF4_ent]

theorem fld12_lt (X o : ℕ) : Nat.land (Nat.shiftRight X o) 4095 < 2 ^ 12 :=
  Nat.and_lt_two_pow _ (by norm_num)

@[expose] noncomputable def rowK (A B i : ℕ) : ℕ :=
  xorN (nat_lit 6) fun k => Nat.xor
    (nIf(bit A (Nat.add (Nat.mul (nat_lit 12) i) (Nat.mul (nat_lit 2) k)),
        fld(B, Nat.mul (nat_lit 12) k, nat_lit 4095), nat_lit 0))
    (nIf(bit A (Nat.succ (Nat.add (Nat.mul (nat_lit 12) i) (Nat.mul (nat_lit 2) k))),
        fld(omK B, Nat.mul (nat_lit 12) k, nat_lit 4095), nat_lit 0))

theorem mulK_eq (A B : ℕ) :
    mulK A B = orN 6 (fun i => Nat.shiftLeft (rowK A B i) (Nat.mul 12 i)) := by
  unfold mulK
  rw [strictN_eq, strictN_eq, strictN_eq]
  rfl

theorem rowK_lt (A B i : ℕ) : rowK A B i < 2 ^ 12 := by
  apply xorN_lt
  intro k
  apply Nat.xor_lt_two_pow
  · cases bit A (Nat.add (Nat.mul 12 i) (Nat.mul 2 k))
    · exact Nat.two_pow_pos 12
    · exact fld12_lt _ _
  · cases bit A (Nat.succ (Nat.add (Nat.mul 12 i) (Nat.mul 2 k)))
    · exact Nat.two_pow_pos 12
    · exact fld12_lt _ _

theorem mulK_lt (A B : ℕ) : mulK A B < 2 ^ 72 := by
  rw [mulK_eq]
  exact orN_lt (w := 12) (c := fun i => rowK A B i) (fun i => rowK_lt A B i) 6

theorem xorN_congr {n : ℕ} {f g : ℕ → ℕ} (h : ∀ i < n, f i = g i) : xorN n f = xorN n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [xorN_succ, xorN_succ, h n (Nat.lt_succ_self n), ih (fun i hi => h i (Nat.lt_succ_of_lt hi))]

theorem fld12_eq (B k : ℕ) : Nat.land (Nat.shiftRight B (Nat.mul 12 k)) 4095 = fget B k 12 := by
  rw [fget_eq]
  change (B >>> (12 * k)) &&& 4095 = _
  rw [show (4095 : ℕ) = 2 ^ 12 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod, Nat.mul_comm]

theorem fm_decomp : ∀ a < 4, ∀ b < 4,
    fm a b = Nat.xor (if a.testBit 0 then b else 0) (if a.testBit 1 then fm 2 b else 0) := by decide

theorem ent_mulK (A B i j : ℕ) (hi : i < 6) (hj : j < 6) :
    ent (mulK A B) i j = xorN 6 (fun k => fm (ent A i k) (ent B k j)) := by
  rw [mulK_eq]
  change fget (orN 6 _) (6 * i + j) 2 = _
  rw [← fget_fget12 _ i j hj, fget_orN (w := 12) (c := fun i => rowK A B i)
    (fun i => rowK_lt A B i) 6 i, if_pos hi]
  unfold rowK
  rw [fget2_xorN]
  apply xorN_congr
  intro k hk
  rw [fget2_xor, fget2_nIf, fget2_nIf, fld12_eq, fld12_eq, fget_fget12 _ _ _ hj,
    fget_fget12 _ _ _ hj, bit_eq, bit_eq]
  have e1 : (ent A i k).testBit 0 = A.testBit (12 * i + 2 * k) := by
    change (fget A (6 * i + k) 2).testBit 0 = _
    rw [testBit_fget2_zero]
    congr 1
    omega
  have e2 : (ent A i k).testBit 1 = A.testBit (12 * i + 2 * k + 1) := by
    change (fget A (6 * i + k) 2).testBit 1 = _
    rw [testBit_fget2_one]
    congr 1
    omega
  have e3 : ent (omK B) k j = fm 2 (ent B k j) := ent_omK B k j hk hj
  have e4 : Nat.add (Nat.mul 12 i) (Nat.mul 2 k) = 12 * i + 2 * k := rfl
  have e5 : Nat.succ (Nat.add (Nat.mul 12 i) (Nat.mul 2 k)) = 12 * i + 2 * k + 1 := rfl
  rw [e5, e4, ← e1, ← e2]
  have e6 : fget (omK B) (6 * k + j) 2 = fm 2 (fget B (6 * k + j) 2) := e3
  rw [e6]
  have := fm_decomp (ent A i k) (fget2_lt _ _) (ent B k j) (fget2_lt _ _)
  rw [this]
  cases (ent A i k).testBit 0 <;> cases (ent A i k).testBit 1 <;> rfl

theorem decM_mulK (A B : ℕ) : decM (mulK A B) = decM A * decM B := by
  rw [← decM_mmul]
  ext i j
  rw [← cF4_ent (mulK A B), ← cF4_ent (mmul A B), ent_mulK A B i j i.2 j.2]
  unfold mmul
  rw [strictN_eq, strictN_eq, cF4_ent_mk]

theorem decM_invK (M : ℕ) : decM (invK M) = ((decM M).map fun a => a ^ 2)ᵀ := by
  unfold invK
  rw [decM_trn, decM_barK]

theorem vecOfCode_apply (c : ℕ) (i : Fin 6) : vecOfCode c i = cF4 (fget c i 2) := by
  have h1 : fget c i 2 = c / 4 ^ (i : ℕ) % 4 := by
    rw [fget2_eq', Nat.shiftRight_eq_div_pow, pow_mul]
    norm_num
  unfold vecOfCode cF4 coord
  rw [h1]
  simp

theorem ent_tvK (v i j : ℕ) (hi : i < 6) (hj : j < 6) :
    ent (tvK v) i j = Nat.xor (ent ONE i j) (fm (fget v i 2) (sqC (fget v j 2))) := by
  unfold tvK
  rw [strictN_eq]
  change fget (Nat.xor ONE _) (6 * i + j) 2 = _
  rw [fget2_xor]
  congr 1
  rw [fget_orN (w := 2)
    (c := fun t => fm (fget v (Nat.div t 6) 2) (sqC (fget v (Nat.mod t 6) 2)))
    (fun t => fm_lt _ _) 36 (6 * i + j), if_pos (by omega)]
  have e1 : Nat.div (6 * i + j) 6 = i := by
    change (6 * i + j) / 6 = i
    omega
  have e2 : Nat.mod (6 * i + j) 6 = j := by
    change (6 * i + j) % 6 = j
    omega
  rw [e1, e2]

theorem decM_tvK (v : ℕ) : decM (tvK v) = tvM (vecOfCode v) := by
  ext i j
  rw [← cF4_ent, ent_tvK v i j i.2 j.2, cF4_xor (ent_lt _ _ _) (fm_lt _ _), cF4_ent ONE i j,
    decM_ONE, fm_spec (b := sqC (fget v j 2)) (fget2_lt _ _) (fm_lt _ _),
    ← cF4_sq (fget2_lt _ _), ← vecOfCode_apply, ← vecOfCode_apply]
  rw [tvM]
  simp [Matrix.add_apply, Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply]

theorem mvK_eq (M x : ℕ) : mvK M x = orN 6 (fun i => Nat.shiftLeft
    (xorN 6 fun j => fm (ent M i j) (fget x j 2)) (Nat.mul 2 i)) := by
  unfold mvK
  rw [strictN_eq, strictN_eq]

theorem mvK_lt (M x : ℕ) : mvK M x < 2 ^ 12 := by
  rw [mvK_eq]
  have h := orN_lt (w := 2) (c := fun i => xorN 6 fun j => fm (ent M i j) (fget x j 2))
    (fun i => xorN_lt (w := 2) (fun j => fm_lt _ _) 6) 6
  have e : (2 : ℕ) ^ (2 * 6) = 2 ^ 12 := by norm_num
  rw [e] at h
  exact h

theorem fget_mvK (M x i : ℕ) (hi : i < 6) :
    fget (mvK M x) i 2 = xorN 6 (fun j => fm (ent M i j) (fget x j 2)) := by
  rw [mvK_eq, fget_orN (w := 2) (c := fun i => xorN 6 fun j => fm (ent M i j) (fget x j 2))
    (fun i => xorN_lt (w := 2) (fun j => fm_lt _ _) 6) 6 i, if_pos hi]

theorem vecOfCode_mvK (M x : ℕ) : vecOfCode (mvK M x) = decM M *ᵥ vecOfCode x := by
  funext i
  rw [vecOfCode_apply, fget_mvK M x i i.2, (xorN_spec _ (fun j => fm_lt _ _) 6).2]
  simp only [Matrix.mulVec, dotProduct]
  rw [← Fin.sum_univ_eq_sum_range (fun k => cF4 (fm (ent M i k) (fget x k 2))) 6]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fm_spec (ent_lt _ _ _) (fget2_lt _ _), cF4_ent, vecOfCode_apply]

theorem vecOfCode_omV (v : ℕ) : vecOfCode (omV v) = (F4.ω : F4) • vecOfCode v := by
  funext i
  rw [vecOfCode_apply, Pi.smul_apply, vecOfCode_apply]
  change cF4 (fget (omB LOV v) i 2) = _
  rw [fget_omB isMask_LOV, if_pos (by have := i.2; omega),
    fm_spec (by norm_num) (fget2_lt _ _), smul_eq_mul]
  rfl

theorem vecOfCode_barV (v : ℕ) : vecOfCode (barV v) = fun i => (vecOfCode v i) ^ 2 := by
  funext i
  rw [vecOfCode_apply, vecOfCode_apply]
  change cF4 (fget (barB LOV v) i 2) = _
  rw [fget_barB isMask_LOV, if_pos (by have := i.2; omega), ← cF4_sq (fget2_lt _ _)]

theorem orB_eq_true {a b : Bool} : orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> simp [orB]

theorem cF4_inj {c d : ℕ} (hc : c < 4) (hd : d < 4) (h : cF4 c = cF4 d) : c = d := by
  have h2 : c % 4 = d % 4 := congrArg (fun x : F4 => x.code.val) h
  rwa [Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hd] at h2

theorem decM_inj {A B : ℕ} (hA : A < 2 ^ 72) (hB : B < 2 ^ 72) (h : decM A = decM B) : A = B := by
  have hent : ∀ k < 36, fget A k 2 = fget B k 2 := by
    intro k hk
    have := congrFun (congrFun h ⟨k / 6, by omega⟩) ⟨k % 6, by omega⟩
    rw [← cF4_ent, ← cF4_ent] at this
    have h2 := cF4_inj (ent_lt _ _ _) (ent_lt _ _ _) this
    have e : 6 * (k / 6) + k % 6 = k := by omega
    change fget A (6 * (k / 6) + k % 6) 2 = fget B (6 * (k / 6) + k % 6) 2 at h2
    rwa [e] at h2
  apply Nat.eq_of_testBit_eq
  intro n
  by_cases hn : n < 72
  · obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · have h1 := congrArg (fun x => Nat.testBit x 0) (hent k (by omega))
      simp only [testBit_fget2_zero] at h1
      exact h1
    · have h1 := congrArg (fun x => Nat.testBit x 1) (hent k (by omega))
      simp only [testBit_fget2_one] at h1
      exact h1
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hA (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hB (Nat.pow_le_pow_right (by norm_num) (by omega)))]

@[expose] def ProjEq (A B : ℕ) : Prop := ∃ c : F4, c ≠ 0 ∧ decM A = c • decM B

theorem eqP_eq (A B : ℕ) : eqP A B = orB (Nat.beq A B)
    (orB (Nat.beq A (omK B)) (Nat.beq A (omK (omK B)))) := by
  unfold eqP
  rw [strictB_eq, strictB_eq, strictB_eq]

theorem omega_ne : (F4.ω : F4) ≠ 0 := by decide

theorem omega_sq_ne : (F4.ω : F4) * F4.ω ≠ 0 := by decide

theorem F4_cases : ∀ c : F4, c ≠ 0 → c = 1 ∨ c = F4.ω ∨ c = F4.ω * F4.ω := by decide

theorem eqP_sound {A B : ℕ} (h : eqP A B = true) : ProjEq A B := by
  rw [eqP_eq, orB_eq_true, orB_eq_true] at h
  rcases h with h | h | h
  · rw [Nat.beq_eq] at h
    exact ⟨1, one_ne_zero, by rw [h, one_smul]⟩
  · rw [Nat.beq_eq] at h
    exact ⟨F4.ω, omega_ne, by rw [h, decM_omK]⟩
  · rw [Nat.beq_eq] at h
    refine ⟨F4.ω * F4.ω, omega_sq_ne, ?_⟩
    rw [h, decM_omK, decM_omK, smul_smul]

theorem eqP_complete {A B : ℕ} (hA : A < 2 ^ 72) (hB : B < 2 ^ 72) (h : ProjEq A B) :
    eqP A B = true := by
  obtain ⟨c, hc, hAB⟩ := h
  rw [eqP_eq, orB_eq_true, orB_eq_true]
  rcases F4_cases c hc with rfl | rfl | rfl
  · left
    rw [Nat.beq_eq]
    exact decM_inj hA hB (by rw [hAB, one_smul])
  · right; left
    rw [Nat.beq_eq]
    exact decM_inj hA (omK_lt B) (by rw [hAB, decM_omK])
  · right; right
    rw [Nat.beq_eq]
    exact decM_inj hA (omK_lt _) (by rw [hAB, decM_omK, decM_omK, smul_smul])

theorem ONE_lt : ONE < 2 ^ 72 := by decide

theorem eqV_eq (u v : ℕ) : eqV u v = orB (Nat.beq u v)
    (orB (Nat.beq u (omV v)) (Nat.beq u (omV (omV v)))) := by
  unfold eqV
  rw [strictB_eq, strictB_eq, strictB_eq]

@[expose] def ProjVec (u v : ℕ) : Prop := ∃ c : F4, c ≠ 0 ∧ vecOfCode u = c • vecOfCode v

theorem vecOfCode_inj {u v : ℕ} (hu : u < 2 ^ 12) (hv : v < 2 ^ 12)
    (h : vecOfCode u = vecOfCode v) : u = v := by
  have h1 := codeOf_vecOfCode (c := u) (by simpa using hu)
  have h2 := codeOf_vecOfCode (c := v) (by simpa using hv)
  rw [← h1, ← h2, h]

theorem eqV_sound {u v : ℕ} (h : eqV u v = true) : ProjVec u v := by
  rw [eqV_eq, orB_eq_true, orB_eq_true] at h
  rcases h with h | h | h
  · rw [Nat.beq_eq] at h
    exact ⟨1, one_ne_zero, by rw [h, one_smul]⟩
  · rw [Nat.beq_eq] at h
    exact ⟨F4.ω, omega_ne, by rw [h, vecOfCode_omV]⟩
  · rw [Nat.beq_eq] at h
    refine ⟨F4.ω * F4.ω, omega_sq_ne, ?_⟩
    rw [h, vecOfCode_omV, vecOfCode_omV, smul_smul]

theorem eqV_complete {u v : ℕ} (hu : u < 2 ^ 12) (hv : v < 2 ^ 12) (h : ProjVec u v) :
    eqV u v = true := by
  obtain ⟨c, hc, huv⟩ := h
  rw [eqV_eq, orB_eq_true, orB_eq_true]
  rcases F4_cases c hc with rfl | rfl | rfl
  · left
    rw [Nat.beq_eq]
    exact vecOfCode_inj hu hv (by rw [huv, one_smul])
  · right; left
    rw [Nat.beq_eq]
    exact vecOfCode_inj hu (omV_lt v) (by rw [huv, vecOfCode_omV])
  · right; right
    rw [Nat.beq_eq]
    exact vecOfCode_inj hu (omV_lt _) (by rw [huv, vecOfCode_omV, vecOfCode_omV, smul_smul])

theorem minK_eq (a b : ℕ) : minK a b = min a b := by
  unfold minK
  by_cases h : a < b
  · have : Nat.blt a b = true := by rw [Nat.blt_eq]; exact h
    rw [this]
    exact (min_eq_left (le_of_lt h)).symm
  · have : Nat.blt a b = false := by
      cases hb : Nat.blt a b
      · rfl
      · rw [Nat.blt_eq] at hb
        exact absurd hb h
    rw [this]
    exact (min_eq_right (not_lt.1 h)).symm

theorem keyK_eq (M : ℕ) : keyK M = min M (min (omK M) (omK (omK M))) := by
  unfold keyK
  rw [strictN_eq, strictN_eq, minK_eq, minK_eq]

theorem omK_cube {N : ℕ} (hN : N < 2 ^ 72) : omK (omK (omK N)) = N := by
  apply decM_inj (omK_lt _) hN
  rw [decM_omK, decM_omK, decM_omK, smul_smul, smul_smul]
  have : (F4.ω : F4) * F4.ω * F4.ω = 1 := by decide
  rw [this, one_smul]

theorem keyK_class {M N : ℕ} (hM : M < 2 ^ 72) (hN : N < 2 ^ 72) (h : ProjEq M N) :
    keyK M = keyK N := by
  have h1 := eqP_complete hM hN h
  rw [eqP_eq, orB_eq_true, orB_eq_true] at h1
  have h3 := omK_cube hN
  rw [keyK_eq, keyK_eq]
  rcases h1 with h1 | h1 | h1
  · rw [Nat.beq_eq] at h1
    rw [h1]
  · rw [Nat.beq_eq] at h1
    rw [h1, h3]
    omega
  · rw [Nat.beq_eq] at h1
    rw [h1, h3]
    omega

end CFSG.KC.U62P.Snd

end
