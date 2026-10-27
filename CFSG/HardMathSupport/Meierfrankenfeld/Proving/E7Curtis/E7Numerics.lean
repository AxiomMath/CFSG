module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis

theorem inner_numerics_e7 {n δ m g : ℕ} (hδ : 1 ≤ δ) (hgn : g ∣ n) (hgδ : g ∣ δ) (hg : 1 ≤ g)
    (h1 : n / g = 1 → 133 ≤ m) (h2 : 2 ≤ n / g → 133 * (n / g) + 1 ≤ m) (hn : 1 ≤ n) :
    133 * n ≤ δ * m := by
  obtain ⟨a, rfl⟩ := hgn
  have ha : g * a / g = a := Nat.mul_div_cancel_left a hg
  have hgδ' : g ≤ δ := Nat.le_of_dvd hδ hgδ
  rw [ha] at h1 h2
  rcases Nat.lt_or_ge a 2 with h | h
  · have ha1 : a = 1 := by
      rcases Nat.eq_zero_or_pos a with h0 | h0
      · subst h0; simp at hn
      · omega
    subst ha1
    have := h1 rfl
    calc 133 * (g * 1) = g * 133 := by ring
      _ ≤ δ * m := Nat.mul_le_mul hgδ' this
  · have := h2 h
    calc 133 * (g * a) ≤ g * (133 * a + 1) := by nlinarith
      _ ≤ δ * m := Nat.mul_le_mul hgδ' this

theorem outer_numerics_e7 {n δ m g : ℕ} (hδ : 1 ≤ δ) (hgn : g ∣ n / 2) (hgδ : g ∣ δ) (hg : 1 ≤ g)
    (hev : Even n) (hn : 1 ≤ n) (h2 : 2 ≤ n / g → 133 * (n / g) + 1 ≤ m) :
    133 * n + 1 ≤ δ * m := by
  obtain ⟨j, hj⟩ := hgn
  obtain ⟨r, hr⟩ := hev
  have hn2 : n / 2 = r := by omega
  rw [hn2] at hj
  have hnj : n = g * (2 * j) := by rw [mul_comm 2 j, ← mul_assoc]; rw [← hj]; omega
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0; simp at hj; omega
    · exact h0
  have ha : n / g = 2 * j := by rw [hnj]; exact Nat.mul_div_cancel_left _ hg
  have hgδ' : g ≤ δ := Nat.le_of_dvd hδ hgδ
  have := h2 (by rw [ha]; omega)
  rw [ha] at this
  calc 133 * n + 1 ≤ g * (133 * (2 * j) + 1) := by rw [hnj]; nlinarith
    _ ≤ δ * m := Nat.mul_le_mul hgδ' this

end CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis
