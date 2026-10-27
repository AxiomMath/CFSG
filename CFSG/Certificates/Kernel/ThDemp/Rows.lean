module

public import CFSG.Certificates.Kernel.Th.Spec.Big

public section

namespace CFSG.Certificates.ThDemp.Rows

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec

theorem rep_succ_eq (x s n : ℕ) : rep x s (n + 1) = rep x s n ||| x <<< (s * n) := rfl

theorem testBit_rep_one (s : ℕ) :
    ∀ m k, (rep 1 s m).testBit k = true ↔ ∃ i < m, k = s * i
  | 0, k => by simp [rep]
  | m + 1, k => by
    rw [rep_succ_eq, Nat.testBit_or, Bool.or_eq_true, testBit_rep_one s m k, Nat.one_shiftLeft,
      Nat.testBit_two_pow, decide_eq_true_iff]
    constructor
    · rintro (⟨i, hi, hk⟩ | h)
      · exact ⟨i, by omega, hk⟩
      · exact ⟨m, by omega, h.symm⟩
    · rintro ⟨i, hi, hk⟩
      by_cases him : i = m
      · right
        subst him
        exact hk.symm
      · left
        exact ⟨i, by omega, hk⟩

theorem testBit_cn (n p : ℕ) :
    (rep 1 256 n).testBit p = decide (p % 256 = 0 ∧ p / 256 < n) := by
  rw [Bool.eq_iff_iff, testBit_rep_one, decide_eq_true_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · intro h
    exact ⟨p / 256, h.2, by omega⟩

theorem rep_lt (s : ℕ) (hs : 0 < s) (m : ℕ) : rep 1 s m < 2 ^ (s * m) := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨i, hi, rfl⟩ := (testBit_rep_one s m j).1 h
  have : s * i < s * m := Nat.mul_lt_mul_of_pos_left hi hs
  omega

theorem add_eq_or_of_land_eq_zero (a b : ℕ) (h : a &&& b = 0) : a + b = a ||| b := by
  by_cases ha : a = 0
  · subst ha
    simp
  · have hlt : a / 2 < a := Nat.div_lt_self (Nat.pos_of_ne_zero ha) (by omega)
    have h' : a / 2 &&& b / 2 = 0 := by rw [← Nat.and_div_two, h]
    have ih := add_eq_or_of_land_eq_zero (a / 2) (b / 2) h'
    have h1 : (a ||| b) / 2 = a / 2 ||| b / 2 := Nat.or_div_two
    have h2 := @Nat.or_mod_two_eq_one a b
    have h3 : ¬ ((a &&& b) % 2 = 1) := by rw [h]; decide
    rw [Nat.and_mod_two_eq_one] at h3
    omega
termination_by a

theorem testBit_mul_pred {u : ℕ} (hu : ∀ q, u.testBit q = true → q % 256 = 0) :
    ∀ n, n ≤ 256 → ∀ p, (u * (2 ^ n - 1)).testBit p =
      (decide (p % 256 < n) && u.testBit (256 * (p / 256)))
  | 0, _, p => by simp
  | n + 1, hn, p => by
    have ih := testBit_mul_pred hu n (by omega)
    have h2 : 2 ^ (n + 1) - 1 = (2 ^ n - 1) + 2 ^ n := by
      have := Nat.one_le_two_pow (n := n)
      rw [Nat.pow_succ]
      omega
    have hb : ∀ q, (u * 2 ^ n).testBit q = (decide (n ≤ q) && u.testBit (q - n)) := fun q => by
      rw [← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]
    have hdis : (u * (2 ^ n - 1)) &&& (u * 2 ^ n) = 0 := by
      apply Nat.eq_of_testBit_eq
      intro q
      rw [Nat.testBit_and, ih, hb, Nat.zero_testBit, Bool.eq_false_iff]
      intro hq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
      obtain ⟨⟨h1, -⟩, h3, h4⟩ := hq
      have := hu _ h4
      omega
    rw [h2, Nat.mul_add, add_eq_or_of_land_eq_zero _ _ hdis, Nat.testBit_or, ih, hb,
      Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨by omega, h2⟩
      · have h0 := hu _ h2
        have e : p - n = 256 * (p / 256) := by omega
        rw [e] at h2
        exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩
      by_cases h3 : p % 256 < n
      · exact Or.inl ⟨h3, h2⟩
      · right
        have e : p - n = 256 * (p / 256) := by omega
        rw [e]
        exact ⟨by omega, h2⟩

theorem testBit_mul_rep {v : ℕ} (hv : v < 2 ^ 256) :
    ∀ n p, (v * rep 1 256 n).testBit p = (decide (p / 256 < n) && v.testBit (p % 256))
  | 0, p => by simp [rep]
  | n + 1, p => by
    have ih := testBit_mul_rep hv n
    have hlt : v * rep 1 256 n < 2 ^ (256 * n) := by
      apply Nat.lt_pow_two_of_testBit
      intro j hj
      rw [ih j]
      have : ¬ j / 256 < n := by omega
      simp [this]
    have hrep : rep 1 256 (n + 1) = rep 1 256 n + 2 ^ (256 * n) := by
      rw [rep_succ_eq, Nat.one_shiftLeft]
      exact Nat.or_two_pow_eq_add_of_lt (rep_lt 256 (by omega) n)
    have e : v * rep 1 256 (n + 1) = (v <<< (256 * n)) ||| (v * rep 1 256 n) := by
      rw [← Nat.shiftLeft_add_eq_or_of_lt hlt, hrep, Nat.mul_add, Nat.shiftLeft_eq, Nat.add_comm]
    rw [e, Nat.testBit_or, testBit_shl_row hv n p, ih p]
    by_cases h1 : p / 256 < n
    · have h3 : ¬ p / 256 = n := by omega
      have h4 : p / 256 < n + 1 := by omega
      simp [h1, h3, h4]
    · by_cases h2 : p / 256 = n
      · simp [h1, h2]
      · have h3 : ¬ p / 256 < n + 1 := by omega
        simp [h1, h2, h3]

@[expose] def xsB (f : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | n + 1 => xsB f n ^^ f n

@[expose] def stepP (c rm A B k : ℕ) : ℕ :=
  ((A >>> k) &&& c) * rm &&& ((B >>> (k * 256)) &&& rm) * c

@[expose] noncomputable def mulBn (c rm A B n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => mstep c rm A B acc k (k * 256)) n

theorem mulB_eq_mulBn (c rm A B : ℕ) : mulB c rm A B = mulBn c rm A B 248 := rfl

theorem mulBn_succ (c rm A B n : ℕ) :
    mulBn c rm A B (n + 1) = mulBn c rm A B n ^^^ stepP c rm A B n := rfl

theorem testBit_stepP {n A B k : ℕ} (p : ℕ) :
    (stepP (rep 1 256 n) (2 ^ 248 - 1) A B k).testBit p =
      (decide (p % 256 < 248 ∧ p / 256 < n) &&
        (A.testBit (256 * (p / 256) + k) && B.testBit (256 * k + p % 256))) := by
  unfold stepP
  rw [Nat.testBit_and]
  have hu : ∀ q, ((A >>> k) &&& rep 1 256 n).testBit q = true → q % 256 = 0 := by
    intro q hq
    rw [Nat.testBit_and, testBit_cn, Bool.and_eq_true, decide_eq_true_eq] at hq
    exact hq.2.1
  have hv : ((B >>> (k * 256)) &&& (2 ^ 248 - 1)) < 2 ^ 256 :=
    Nat.lt_of_lt_of_le (Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos _) (by omega)))
      (Nat.pow_le_pow_right (by omega) (by omega))
  rw [testBit_mul_pred hu 248 (by omega), testBit_mul_rep hv n, Nat.testBit_and,
    Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftRight, testBit_cn,
    Nat.testBit_two_pow_sub_one]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  have e1 : 256 * (p / 256) % 256 = 0 := by omega
  have e2 : 256 * (p / 256) / 256 = p / 256 := by omega
  rw [e1, e2, Nat.add_comm k, Nat.mul_comm k]
  simp only [true_and]
  tauto

theorem testBit_mulBn {n A B : ℕ} (p : ℕ) : ∀ m, m ≤ 248 →
    (mulBn (rep 1 256 n) (2 ^ 248 - 1) A B m).testBit p =
      (decide (p % 256 < 248 ∧ p / 256 < n) &&
        xsB (fun k => A.testBit (256 * (p / 256) + k) && B.testBit (256 * k + p % 256)) m)
  | 0, _ => by simp [mulBn, xsB]
  | m + 1, hm => by
    rw [mulBn_succ, Nat.testBit_xor, testBit_mulBn p m (by omega), testBit_stepP p, xsB]
    cases decide (p % 256 < 248 ∧ p / 256 < n) <;> simp

theorem testBit_mulB_rows (n A B p : ℕ) :
    (mulB (rep 1 256 n) (2 ^ 248 - 1) A B).testBit p =
      (decide (p % 256 < 248 ∧ p / 256 < n) &&
        xsB (fun k => A.testBit (256 * (p / 256) + k) && B.testBit (256 * k + p % 256)) 248) := by
  rw [mulB_eq_mulBn, testBit_mulBn p 248 le_rfl]

@[expose] noncomputable def vecBn (rm v M m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun k acc => Nat.xor acc (Nat.mul (Nat.land (Nat.shiftRight v k) 1)
      (Nat.land (Nat.shiftRight M (Nat.mul k 256)) rm))) m

theorem vecB_eq_vecBn (rm v M : ℕ) : vecB rm v M = vecBn rm v M 248 := rfl

theorem vecBn_succ (rm v M m : ℕ) : vecBn rm v M (m + 1) =
    vecBn rm v M m ^^^ (((v >>> m) &&& 1) * ((M >>> (m * 256)) &&& rm)) := rfl

theorem testBit_vecTerm (v M m j : ℕ) :
    (((v >>> m) &&& 1) * ((M >>> (m * 256)) &&& (2 ^ 248 - 1))).testBit j =
      (v.testBit m && (M.testBit (256 * m + j) && decide (j < 248))) := by
  have h1 : (v >>> m) &&& 1 = if v.testBit m then 1 else 0 := by
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ m) with h | h <;> simp [h]
  rw [h1]
  cases hb : v.testBit m
  · simp
  · simp only [if_true, Nat.one_mul, Bool.true_and]
    rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, Nat.mul_comm m 256,
      Nat.add_comm (256 * m)]

theorem testBit_vecBn (v M j : ℕ) : ∀ m, m ≤ 248 →
    (vecBn (2 ^ 248 - 1) v M m).testBit j = (decide (j < 248) &&
      xsB (fun k => v.testBit k && M.testBit (256 * k + j)) m)
  | 0, _ => by simp [vecBn, xsB]
  | m + 1, hm => by
    rw [vecBn_succ, Nat.testBit_xor, testBit_vecBn v M j m (by omega), testBit_vecTerm, xsB]
    cases decide (j < 248) <;> cases v.testBit m <;> cases M.testBit (256 * m + j) <;>
      cases xsB (fun k => v.testBit k && M.testBit (256 * k + j)) m <;> rfl

theorem testBit_vecB (v M j : ℕ) : (vecB (2 ^ 248 - 1) v M).testBit j = (decide (j < 248) &&
    xsB (fun k => v.testBit k && M.testBit (256 * k + j)) 248) := by
  rw [vecB_eq_vecBn, testBit_vecBn v M j 248 le_rfl]

theorem xsB_congr {f g : ℕ → Bool} : ∀ m, (∀ k < m, f k = g k) → xsB f m = xsB g m
  | 0, _ => rfl
  | m + 1, h => by
    rw [xsB, xsB, xsB_congr m (fun k hk => h k (by omega)), h m (by omega)]

theorem row_mulB {n r : ℕ} (hr : r < n) (A B : ℕ) :
    (mulB (rep 1 256 n) (2 ^ 248 - 1) A B >>> (256 * r)) &&& (2 ^ 248 - 1) =
      vecB (2 ^ 248 - 1) ((A >>> (256 * r)) &&& (2 ^ 248 - 1)) B := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, testBit_mulB_rows,
    testBit_vecB]
  by_cases hj : j < 248
  · have e1 : (256 * r + j) % 256 = j := by omega
    have e2 : (256 * r + j) / 256 = r := by omega
    rw [e1, e2]
    simp only [hj, hr, and_self, decide_true, Bool.true_and, Bool.and_true]
    refine xsB_congr 248 fun k hk => ?_
    rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
    simp [hk, Nat.add_comm k]
  · simp [hj]

theorem mulB_lt (n A B : ℕ) : mulB (rep 1 256 n) (2 ^ 248 - 1) A B < 2 ^ (256 * n) := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  rw [testBit_mulB_rows]
  have : ¬ j / 256 < n := by
    intro h
    have := Nat.lt_of_lt_of_le (Nat.lt_mul_div_succ j (by omega : 0 < 256)) (Nat.mul_le_mul_left 256 h)
    omega
  simp [this]

end CFSG.Certificates.ThDemp.Rows

end
