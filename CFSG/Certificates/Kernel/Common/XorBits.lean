module

public import Mathlib.Data.Nat.Notation

public section

namespace CFSG.KC.XorBits

@[expose] def xorB (f : ℕ → ℕ) (x : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => xorB f x k ^^^ (if x.testBit k then f k else 0)

theorem xorB_succ (f : ℕ → ℕ) (x k : ℕ) :
    xorB f x (k + 1) = xorB f x k ^^^ (if x.testBit k then f k else 0) := rfl

theorem xor_xor_cancel (a b c : ℕ) : a ^^^ c ^^^ (b ^^^ c) = a ^^^ b := by
  rw [Nat.xor_assoc, Nat.xor_comm b c, ← Nat.xor_assoc c c b, Nat.xor_self, Nat.zero_xor]

theorem xor_right_comm (a b c : ℕ) : a ^^^ b ^^^ c = a ^^^ c ^^^ b := by
  rw [Nat.xor_assoc, Nat.xor_comm b c, ← Nat.xor_assoc]

theorem xor_xor_xor (a b c d : ℕ) : a ^^^ b ^^^ (c ^^^ d) = a ^^^ c ^^^ (b ^^^ d) := by
  rw [Nat.xor_assoc, ← Nat.xor_assoc b c d, Nat.xor_comm b c, Nat.xor_assoc c b d,
    ← Nat.xor_assoc a c]

theorem xorB_zero (f : ℕ → ℕ) : ∀ k, xorB f 0 k = 0
  | 0 => rfl
  | k + 1 => by simp [xorB_succ, xorB_zero f k]

theorem xorB_xor (f : ℕ → ℕ) (x y : ℕ) : ∀ k, xorB f (x ^^^ y) k = xorB f x k ^^^ xorB f y k
  | 0 => (Nat.xor_self 0).symm
  | k + 1 => by
    rw [xorB_succ, xorB_succ, xorB_succ, xorB_xor f x y k, Nat.testBit_xor]
    cases x.testBit k <;> cases y.testBit k
    · simp
    · simp [Nat.xor_assoc]
    · simpa using xor_right_comm (xorB f x k) (xorB f y k) (f k)
    · simpa using (xor_xor_cancel (xorB f x k) (xorB f y k) (f k)).symm

theorem map_zero_of_xor {P : ℕ → ℕ} (hP : ∀ a b, P (a ^^^ b) = P a ^^^ P b) : P 0 = 0 := by
  have h := hP 0 0
  rwa [Nat.xor_self, Nat.xor_self] at h

theorem xorB_hom {P : ℕ → ℕ} (hP : ∀ a b, P (a ^^^ b) = P a ^^^ P b) (f : ℕ → ℕ) (x : ℕ) :
    ∀ k, P (xorB f x k) = xorB (fun i => P (f i)) x k
  | 0 => map_zero_of_xor hP
  | k + 1 => by
    rw [xorB_succ, xorB_succ, hP, xorB_hom hP f x k]
    by_cases h : x.testBit k = true
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h, map_zero_of_xor hP]

theorem xorB_two_pow_mod (x : ℕ) : ∀ k, xorB (fun i => 2 ^ i) x k = x % 2 ^ k
  | 0 => by rw [Nat.pow_zero, Nat.mod_one]; rfl
  | k + 1 => by
    rw [xorB_succ, xorB_two_pow_mod x k]
    refine Nat.eq_of_testBit_eq fun i => ?_
    rw [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases h : x.testBit k = true
    · rw [ite_eq_left h, Nat.testBit_two_pow]
      rcases Nat.lt_trichotomy i k with hi | rfl | hi
      · have h1 : i < k + 1 := by omega
        have h3 : k ≠ i := by omega
        simp [hi, h1, h3]
      · simp [h]
      · have h1 : ¬ i < k + 1 := by omega
        have h2 : ¬ i < k := by omega
        have h3 : k ≠ i := by omega
        simp [h1, h2, h3]
    · rw [ite_eq_right h, Nat.zero_testBit, Bool.xor_false]
      rcases Nat.lt_trichotomy i k with hi | rfl | hi
      · have h1 : i < k + 1 := by omega
        simp [hi, h1]
      · simp [h]
      · have h1 : ¬ i < k + 1 := by omega
        have h2 : ¬ i < k := by omega
        simp [h1, h2]

theorem xorB_two_pow {x k : ℕ} (hx : x < 2 ^ k) : xorB (fun i => 2 ^ i) x k = x := by
  rw [xorB_two_pow_mod, Nat.mod_eq_of_lt hx]

theorem xorB_congr (f : ℕ → ℕ) {x y : ℕ} :
    ∀ k, (∀ i < k, x.testBit i = y.testBit i) → xorB f x k = xorB f y k
  | 0, _ => rfl
  | k + 1, h => by
    rw [xorB_succ, xorB_succ, xorB_congr f k fun i hi => h i (Nat.lt_succ_of_lt hi),
      h k (Nat.lt_succ_self k)]

theorem xorB_mod (f : ℕ → ℕ) (x k : ℕ) : xorB f (x % 2 ^ k) k = xorB f x k :=
  xorB_congr f k fun i hi => by rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and]

theorem xorB_xor_fun (f g : ℕ → ℕ) (x : ℕ) :
    ∀ k, xorB (fun i => f i ^^^ g i) x k = xorB f x k ^^^ xorB g x k
  | 0 => (Nat.xor_self 0).symm
  | k + 1 => by
    rw [xorB_succ, xorB_succ, xorB_succ, xorB_xor_fun f g x k]
    by_cases h : x.testBit k = true
    · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h]
      exact xor_xor_xor _ _ _ _
    · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h, Nat.xor_zero, Nat.xor_zero, Nat.xor_zero]

theorem xorB_congr_fun {f g : ℕ → ℕ} (x : ℕ) :
    ∀ k, (∀ i < k, f i = g i) → xorB f x k = xorB g x k
  | 0, _ => rfl
  | k + 1, h => by
    rw [xorB_succ, xorB_succ, xorB_congr_fun x k fun i hi => h i (Nat.lt_succ_of_lt hi),
      h k (Nat.lt_succ_self k)]

theorem xorB_lt {f : ℕ → ℕ} {w : ℕ} (hf : ∀ i, f i < 2 ^ w) (x : ℕ) : ∀ k, xorB f x k < 2 ^ w
  | 0 => Nat.two_pow_pos w
  | k + 1 => by
    rw [xorB_succ]
    refine Nat.xor_lt_two_pow (xorB_lt hf x k) ?_
    by_cases h : x.testBit k = true
    · rw [ite_eq_left h]
      exact hf k
    · rw [ite_eq_right h]
      exact Nat.two_pow_pos w

theorem xorB_add (f : ℕ → ℕ) (x k : ℕ) :
    ∀ l, xorB f x (k + l) = xorB f x k ^^^ xorB (fun j => f (k + j)) (x >>> k) l
  | 0 => by rw [Nat.add_zero, xorB, Nat.xor_zero]
  | l + 1 => by
    rw [← Nat.add_assoc, xorB_succ, xorB_add f x k l, xorB_succ, Nat.testBit_shiftRight,
      Nat.xor_assoc]

end CFSG.KC.XorBits
