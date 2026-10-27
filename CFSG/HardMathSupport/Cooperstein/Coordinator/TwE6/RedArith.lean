module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

theorem win_inner {f δ g r m : ℕ} (hg : g ∣ δ) (hδ : 1 ≤ δ) (hr : g * r = 2 * f)
    (hm : 39 * r ≤ m) : 78 * f ≤ δ * m := by
  have hgδ : g ≤ δ := Nat.le_of_dvd hδ hg
  calc 78 * f = g * (39 * r) := by nlinarith
    _ ≤ δ * m := Nat.mul_le_mul hgδ hm

theorem win_outer {f δ g r m : ℕ} (hg : g ∣ δ) (hδ : 1 ≤ δ) (hg1 : 1 ≤ g) (hr : g * r = 2 * f)
    (hm : 39 * r + 1 ≤ m) : 78 * f + 1 ≤ δ * m := by
  have hgδ : g ≤ δ := Nat.le_of_dvd hδ hg
  calc 78 * f + 1 ≤ g * (39 * r + 1) := by nlinarith
    _ ≤ δ * m := Nat.mul_le_mul hgδ hm

theorem win_outer_79 {f δ m : ℕ} (hg : f ∣ δ) (hδ : 1 ≤ δ) (hf : 1 ≤ f) (hm : 79 ≤ m) :
    78 * f + 1 ≤ δ * m := by
  have hgδ : f ≤ δ := Nat.le_of_dvd hδ hg
  calc 78 * f + 1 ≤ f * 79 := by nlinarith
    _ ≤ δ * m := Nat.mul_le_mul hgδ hm

theorem survivor_numerics {n δ m c e : ℕ} (hδ : 1 ≤ δ) (hnδ : n ∣ δ) (hcm : c ≤ m)
    (hoff : 2 ^ (δ * m) ≤ e * 2 ^ (δ * c)) (hs : e * (2 ^ n) ^ c < (2 ^ n) ^ m) : False := by
  obtain ⟨r, rfl⟩ := hnδ
  have hr : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · subst h0; simp at hδ
    · exact h0
  have h1 : 2 ^ (n * r * m) = 2 ^ (n * r * (m - c)) * 2 ^ (n * r * c) := by
    rw [← pow_add]
    congr 1
    rw [← Nat.mul_add]
    congr 1
    omega
  rw [h1] at hoff
  have h2 : 2 ^ (n * r * (m - c)) ≤ e :=
    Nat.le_of_mul_le_mul_right hoff (by positivity)
  have h3 : 2 ^ (n * (m - c)) ≤ 2 ^ (n * r * (m - c)) := by
    apply Nat.pow_le_pow_right (by norm_num)
    calc n * (m - c) = n * 1 * (m - c) := by ring
      _ ≤ n * r * (m - c) := by gcongr
  have h4 : (2 ^ n) ^ m = 2 ^ (n * (m - c)) * (2 ^ n) ^ c := by
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    rw [← Nat.mul_add]
    congr 1
    omega
  rw [h4] at hs
  have h5 : 2 ^ (n * (m - c)) * (2 ^ n) ^ c ≤ e * (2 ^ n) ^ c :=
    Nat.mul_le_mul_right _ (h3.trans h2)
  omega

end CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6
