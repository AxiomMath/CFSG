module

public import CFSG.Certificates.Kernel.CoPairSound
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.KC.Co2Mem

open CFSG.Monster.VisCert.Native CFSG.KC.CoPair

theorem actGo_succ (rows : Array ℕ) (v n : ℕ) :
    actGo rows v (n + 1) 0 = (if v.testBit n then rows[n]! else 0) ^^^ actGo rows v n 0 := by
  rw [actGo, actGo_acc]
  split <;> simp

theorem actGo_hom {F : ℕ → ℕ} (hF : ∀ a b, F (a ^^^ b) = F a ^^^ F b) {N C : Array ℕ} (y : ℕ) :
    ∀ n, (∀ t < n, C[t]! = F N[t]!) → F (actGo N y n 0) = actGo C y n 0 := by
  have h0 : F 0 = 0 := by
    have := hF 0 0
    rwa [Nat.xor_self, Nat.xor_self] at this
  intro n
  induction n with
  | zero => intro _; simpa [actGo] using h0
  | succ n ih =>
    intro hC
    rw [actGo_succ, actGo_succ, hF, ih fun t ht => hC t (by omega)]
    congr 1
    split
    · exact (hC n (by omega)).symm
    · exact h0

theorem actGo_unit_bit {C : Array ℕ} (y : ℕ) : ∀ n, (∀ t < n, C[t]! = 2 ^ t) → ∀ j,
    (actGo C y n 0).testBit j = (decide (j < n) && y.testBit j) := by
  intro n
  induction n with
  | zero => intro _ j; simp [actGo]
  | succ n ih =>
    intro hC j
    rw [actGo_succ, hC n (by omega), Nat.testBit_xor, ih (fun t ht => hC t (by omega))]
    by_cases hj : j = n
    · subst hj
      split <;> simp_all [Nat.testBit_two_pow_self]
    · have : (decide (j < n + 1)) = decide (j < n) := by
        by_cases h' : j < n
        · simp [h', show j < n + 1 by omega]
        · simp [h', show ¬ j < n + 1 by omega]
      rw [this]
      split <;> simp [Ne.symm hj]

theorem actGo_unit {C : Array ℕ} {n : ℕ} (hC : ∀ t < n, C[t]! = 2 ^ t) {y : ℕ} (hy : y < 2 ^ n) :
    actGo C y n 0 = y := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [actGo_unit_bit y n hC j]
  by_cases hj : j < n
  · simp [hj]
  · simp only [hj, decide_false, Bool.false_and]
    exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hy
      (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm

theorem actGo_lt {rows : Array ℕ} {w : ℕ} (v : ℕ) :
    ∀ n, (∀ t < n, rows[t]! < 2 ^ w) → actGo rows v n 0 < 2 ^ w := by
  intro n
  induction n with
  | zero => intro _; simp [actGo]
  | succ n ih =>
    intro hr
    rw [actGo_succ]
    refine Nat.xor_lt_two_pow ?_ (ih fun t ht => hr t (by omega))
    split
    · exact hr n (by omega)
    · exact Nat.two_pow_pos w

theorem xor_ne_zero_of {r x h : ℕ} (h1 : 2 ^ h ≤ r) (h2 : r < 2 ^ (h + 1)) (hx : x < 2 ^ h) :
    r ^^^ x ≠ 0 := by
  intro e
  have hr : r >>> h = 1 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.pow_succ] at *
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  have hx' : x >>> h = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt hx
  have : (r ^^^ x) >>> h = 1 := by
    rw [Nat.shiftRight_xor_distrib, hr, hx', Nat.xor_zero]
  rw [e, Nat.zero_shiftRight] at this
  exact absurd this (by decide)

theorem actGo_echelon {O : Array ℕ} {h : ℕ → ℕ} {k : ℕ} (hz : ∀ i < k, O[i]! = 0)
    {n : ℕ} (hb : ∀ i, k ≤ i → i < n → 2 ^ h i ≤ O[i]! ∧ O[i]! < 2 ^ (h i + 1))
    (hh : ∀ i, k ≤ i → i + 1 < n → h i < h (i + 1)) (z : ℕ) :
    (n ≤ k → actGo O z n 0 = 0) ∧ (k < n → actGo O z n 0 < 2 ^ (h (n - 1) + 1)) ∧
      (actGo O z n 0 = 0 → ∀ i, k ≤ i → i < n → z.testBit i = false) := by
  induction n with
  | zero => exact ⟨fun _ => by simp [actGo], fun h' => absurd h' (Nat.not_lt_zero _),
      fun _ i _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨i1, i2, i3⟩ :=
      ih (fun i h1 h2 => hb i h1 (by omega)) (fun i h1 h2 => hh i h1 (by omega))
    rw [actGo_succ]
    rcases Nat.lt_or_ge n k with hnk | hnk
    · have hO : O[n]! = 0 := hz n hnk
      have hX : actGo O z n 0 = 0 := i1 (by omega)
      refine ⟨fun _ => by simp [hO, hX], fun h' => absurd h' (by omega), fun _ i h1 h2 => by omega⟩
    · obtain ⟨b1, b2⟩ := hb n hnk (by omega)
      have hX : actGo O z n 0 < 2 ^ h n := by
        rcases Nat.lt_or_ge k n with hkn | hkn
        · have := i2 hkn
          have hm : h (n - 1) + 1 ≤ h n := by
            have := hh (n - 1) (by omega) (by omega)
            rw [Nat.sub_add_cancel (by omega)] at this
            omega
          exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) (by omega))
        · rw [i1 (by omega)]
          exact Nat.two_pow_pos _
      have hX' : actGo O z n 0 < 2 ^ (h n + 1) :=
        lt_of_lt_of_le hX (Nat.pow_le_pow_right (by norm_num) (by omega))
      refine ⟨fun h' => absurd h' (by omega), fun _ => ?_, fun e i h1 h2 => ?_⟩
      · split
        · exact Nat.xor_lt_two_pow b2 hX'
        · rw [Nat.zero_xor]
          exact hX'
      · by_cases hzn : z.testBit n = true
        · simp only [hzn, ite_true] at e
          exact absurd e (xor_ne_zero_of b1 b2 hX)
        · simp only [hzn, Bool.false_eq_true, ite_false, Nat.zero_xor] at e
          rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | rfl
          · exact i3 e i h1 h2
          · simpa using hzn

end CFSG.KC.Co2Mem

end
