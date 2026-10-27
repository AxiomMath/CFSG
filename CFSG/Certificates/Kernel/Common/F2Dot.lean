module

public import Aesop.BuiltinRules
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Push

public section

namespace CFSG.KC.F2Dot

@[expose] def dotFrom (e a : ℕ) : ℕ → ℕ → Bool
  | _, 0 => false
  | k, m + 1 => (e.testBit k && a.testBit k) ^^ dotFrom e a (k + 1) m

@[expose] def maskFrom (f : ℕ → Bool) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | k, m + 1 => (if f k then 2 ^ k else 0) ||| maskFrom f (k + 1) m

@[expose] def xorL (L : List ℕ) : ℕ := L.foldr (· ^^^ ·) 0

theorem dotFrom_congr {e a a' : ℕ} :
    ∀ (m k : ℕ), (∀ i, k ≤ i → i < k + m → a.testBit i = a'.testBit i) →
      dotFrom e a k m = dotFrom e a' k m
  | 0, _, _ => rfl
  | m + 1, k, h => by
    simp only [dotFrom]
    rw [h k le_rfl (by omega), dotFrom_congr m (k + 1) fun i h1 h2 => h i (by omega) (by omega)]

theorem dotFrom_xor (e a b : ℕ) :
    ∀ (m k : ℕ), dotFrom e (a ^^^ b) k m = (dotFrom e a k m ^^ dotFrom e b k m)
  | 0, _ => rfl
  | m + 1, k => by
    simp only [dotFrom, Nat.testBit_xor, dotFrom_xor e a b m (k + 1)]
    cases e.testBit k <;> cases a.testBit k <;> cases b.testBit k <;>
      cases dotFrom e a (k + 1) m <;> cases dotFrom e b (k + 1) m <;> rfl

theorem dotFrom_zero (e : ℕ) : ∀ (m k : ℕ), dotFrom e 0 k m = false
  | 0, _ => rfl
  | m + 1, k => by simp [dotFrom, dotFrom_zero e m (k + 1)]

theorem dotFrom_xorL (e : ℕ) (m k : ℕ) :
    ∀ L : List ℕ, (∀ a ∈ L, dotFrom e a k m = false) → dotFrom e (xorL L) k m = false
  | [], _ => dotFrom_zero e m k
  | a :: L, h => by
    change dotFrom e (a ^^^ xorL L) k m = false
    rw [dotFrom_xor, h a List.mem_cons_self,
      dotFrom_xorL e m k L fun b hb => h b (List.mem_cons_of_mem _ hb)]
    rfl

theorem dotFrom_two_pow (e p : ℕ) :
    ∀ (m k : ℕ), k ≤ p → p < k + m → dotFrom e (2 ^ p) k m = e.testBit p
  | 0, _, h1, h2 => by omega
  | m + 1, k, h1, h2 => by
    simp only [dotFrom, Nat.testBit_two_pow]
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · have : dotFrom e (2 ^ k) (k + 1) m = false := by
        rw [dotFrom_congr (a' := 0) m (k + 1) fun i h1 _ => by
          simp only [Nat.testBit_two_pow, Nat.zero_testBit, decide_eq_false_iff_not]; omega]
        exact dotFrom_zero e m (k + 1)
      simp [this]
    · rw [dotFrom_two_pow e p m (k + 1) (by omega) (by omega)]
      have hpk : (p = k) = False := propext ⟨fun h => by omega, False.elim⟩
      simp [hpk]

theorem testBit_maskFrom (f : ℕ → Bool) :
    ∀ (m k i : ℕ), (maskFrom f k m).testBit i = (decide (k ≤ i ∧ i < k + m) && f i)
  | 0, k, i => by
    simp only [maskFrom, Nat.zero_testBit, Nat.add_zero]
    by_cases h : k ≤ i <;> simp [h]
    omega
  | m + 1, k, i => by
    simp only [maskFrom, Nat.testBit_or, testBit_maskFrom f m (k + 1) i]
    by_cases hik : i = k
    · subst hik
      cases hf : f i <;> simp [hf, Nat.testBit_two_pow]
    · have h1 : (if f k = true then 2 ^ k else 0).testBit i = false := by
        split
        · rw [Nat.testBit_two_pow]; simp; omega
        · exact Nat.zero_testBit i
      rw [h1, Bool.false_or]
      congr 1
      simp only [decide_eq_decide]
      omega

theorem testBit_eq_false_of_xorL {e p m k : ℕ} {L : List ℕ} (hL : xorL L = 2 ^ p) (hp1 : k ≤ p)
    (hp2 : p < k + m) (h0 : ∀ a ∈ L, dotFrom e a k m = false) : e.testBit p = false := by
  rw [← dotFrom_two_pow e p m k hp1 hp2, ← hL]
  exact dotFrom_xorL e m k L h0

end CFSG.KC.F2Dot
