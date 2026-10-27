module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Basic
public import Mathlib.Tactic.Attr.Core

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

@[expose] def xorBits (n : ℕ) (f : ℕ → ℕ) (v : ℕ) : ℕ :=
  (List.range n).foldl (fun r j => if v.testBit j then r ^^^ f j else r) 0

theorem xorBits_succ (n : ℕ) (f : ℕ → ℕ) (v : ℕ) :
    xorBits (n + 1) f v = xorBits n f v ^^^ (if v.testBit n then f n else 0) := by
  unfold xorBits
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  split <;> simp

theorem xorBits_zero (f : ℕ → ℕ) (v : ℕ) : xorBits 0 f v = 0 := rfl

theorem xorBits_two_pow (n v : ℕ) : xorBits n (fun j => 2 ^ j) v = v % 2 ^ n := by
  induction n with
  | zero => simp [xorBits_zero, Nat.mod_one]
  | succ n ih =>
    rw [xorBits_succ, ih]
    refine Nat.eq_of_testBit_eq fun i => ?_
    rw [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    split
    · rename_i h
      rw [Nat.testBit_two_pow]
      by_cases hi : i < n
      · simp [hi, show n ≠ i by omega, show i < n + 1 by omega]
      · by_cases hin : i = n
        · subst hin; simp [h]
        · simp [hi, show ¬ i < n + 1 by omega, Ne.symm hin]
    · rename_i h
      simp only [Nat.zero_testBit, Bool.xor_false]
      by_cases hi : i < n
      · simp [hi, show i < n + 1 by omega]
      · by_cases hin : i = n
        · subst hin; simp [h]
        · simp [hi, show ¬ i < n + 1 by omega]

theorem xorBits_two_pow_of_lt {n v : ℕ} (hv : v < 2 ^ n) : xorBits n (fun j => 2 ^ j) v = v := by
  rw [xorBits_two_pow, Nat.mod_eq_of_lt hv]

theorem xorBits_lt {n : ℕ} {f : ℕ → ℕ} (hf : ∀ j, j < n → f j < 2 ^ n) (v : ℕ) :
    xorBits n f v < 2 ^ n := by
  unfold xorBits
  have key : ∀ (l : List ℕ) (r : ℕ), r < 2 ^ n → (∀ j ∈ l, j < n) →
      l.foldl (fun r j => if v.testBit j then r ^^^ f j else r) r < 2 ^ n := by
    intro l
    induction l with
    | nil => intro r hr _; exact hr
    | cons a l ih =>
      intro r hr hl
      rw [List.foldl_cons]
      refine ih _ ?_ fun j hj => hl j (List.mem_cons_of_mem _ hj)
      split
      · exact Nat.xor_lt_two_pow hr (hf a (hl a List.mem_cons_self))
      · exact hr
  exact key _ 0 (Nat.two_pow_pos n) fun j hj => List.mem_range.1 hj

theorem eq_xorBits {n : ℕ} {F : ℕ → ℕ}
    (hF : ∀ v w, v < 2 ^ n → w < 2 ^ n → F (v ^^^ w) = F v ^^^ F w) {v : ℕ} (hv : v < 2 ^ n) :
    F v = xorBits n (fun j => F (2 ^ j)) v := by
  have h0 : F 0 = 0 := by
    have := hF 0 0 (Nat.two_pow_pos n) (Nat.two_pow_pos n)
    rw [Nat.xor_self] at this
    have h2 : F 0 ^^^ F 0 = 0 := Nat.xor_self _
    rw [← this] at h2
    exact h2
  have key : ∀ m, m ≤ n → F (xorBits m (fun j => 2 ^ j) v) = xorBits m (fun j => F (2 ^ j)) v := by
    intro m
    induction m with
    | zero => intro _; rw [xorBits_zero, xorBits_zero, h0]
    | succ m ih =>
      intro hm
      have hlt : ∀ k, k ≤ n → xorBits k (fun j => 2 ^ j) v < 2 ^ n := fun k hk => by
        rw [xorBits_two_pow]
        exact lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
          (Nat.pow_le_pow_right Nat.two_pos hk)
      rw [xorBits_succ, xorBits_succ, ← ih (by omega)]
      split
      · rw [hF _ _ (hlt m (by omega)) (Nat.pow_lt_pow_right Nat.one_lt_two (by omega))]
      · rw [Nat.xor_zero, Nat.xor_zero]
  rw [← key n le_rfl, xorBits_two_pow_of_lt hv]

end CFSG.EvenSmallLie.OmegaEight.SpBranch
