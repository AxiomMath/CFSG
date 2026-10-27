module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.OddStandard.GH71.S55.C5

variable {p q : ℕ}

theorem natCast_ne_zero_of_lt {n : ℕ} (h0 : 0 < n) (hn : n < p) : ((n : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  exact absurd (Nat.le_of_dvd h0 h) (by omega)

theorem not_dvd_pow {r f : ℕ} (hp : p.Prime) (hr : r.Prime) (hrp : r ≠ p) : ¬ p ∣ r ^ f := by
  intro h
  exact hrp ((Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow h)).symm

theorem cast_cyc (hq : 1 ≤ q) :
    ((q - 1 : ℕ) : ZMod p) = (q : ZMod p) - 1 ∧
      ((q ^ 2 - q + 1 : ℕ) : ZMod p) = (q : ZMod p) ^ 2 - q + 1 ∧
      ((q ^ 4 - q ^ 2 + 1 : ℕ) : ZMod p) = (q : ZMod p) ^ 4 - (q : ZMod p) ^ 2 + 1 := by
  refine ⟨by rw [Nat.cast_sub hq, Nat.cast_one], ?_, ?_⟩
  · rw [Nat.cast_add, Nat.cast_sub (Nat.le_self_pow two_ne_zero q), Nat.cast_pow, Nat.cast_one]
  · rw [Nat.cast_add, Nat.cast_sub (Nat.pow_le_pow_right hq (by norm_num)), Nat.cast_pow,
      Nat.cast_pow, Nat.cast_one]

theorem cyc1_excl (hp5 : 5 ≤ p) (hq : 1 ≤ q) (h : p ∣ q - 1) :
    ¬ p ∣ q ∧ ¬ p ∣ q + 1 ∧ ¬ p ∣ q ^ 2 + q + 1 ∧ ¬ p ∣ q ^ 2 + 1 ∧ ¬ p ∣ q ^ 2 - q + 1 ∧
      ¬ p ∣ q ^ 4 - q ^ 2 + 1 := by
  obtain ⟨c1, c6, c12⟩ := cast_cyc (p := p) hq
  simp only [← ZMod.natCast_eq_zero_iff, c1, c6, c12] at h ⊢
  push_cast at h ⊢
  set x := (q : ZMod p)
  refine ⟨fun h' => ?_, fun h' => ?_, fun h' => ?_, fun h' => ?_, fun h' => ?_, fun h' => ?_⟩
  · exact natCast_ne_zero_of_lt (p := p) (n := 1) (by norm_num) (by omega)
      (by push_cast; linear_combination h' - h)
  · exact natCast_ne_zero_of_lt (p := p) (n := 2) (by norm_num) (by omega)
      (by push_cast; linear_combination h' - h)
  · exact natCast_ne_zero_of_lt (p := p) (n := 3) (by norm_num) (by omega)
      (by push_cast; linear_combination h' - (x + 2) * h)
  · exact natCast_ne_zero_of_lt (p := p) (n := 2) (by norm_num) (by omega)
      (by push_cast; linear_combination h' - (x + 1) * h)
  · exact natCast_ne_zero_of_lt (p := p) (n := 1) (by norm_num) (by omega)
      (by push_cast; linear_combination h' - x * h)
  · exact natCast_ne_zero_of_lt (p := p) (n := 1) (by norm_num) (by omega)
      (by push_cast; linear_combination h' - (x ^ 3 + x ^ 2) * h)

theorem cyc2_excl (hp5 : 5 ≤ p) (hq : 1 ≤ q) (h : p ∣ q + 1) :
    ¬ p ∣ q ∧ ¬ p ∣ q - 1 ∧ ¬ p ∣ q ^ 2 + q + 1 ∧ ¬ p ∣ q ^ 2 + 1 ∧ ¬ p ∣ q ^ 2 - q + 1 ∧
      ¬ p ∣ q ^ 4 - q ^ 2 + 1 := by
  obtain ⟨c1, c6, c12⟩ := cast_cyc (p := p) hq
  simp only [← ZMod.natCast_eq_zero_iff, c1, c6, c12] at h ⊢
  push_cast at h ⊢
  set x := (q : ZMod p)
  refine ⟨fun h' => ?_, fun h' => ?_, fun h' => ?_, fun h' => ?_, fun h' => ?_, fun h' => ?_⟩
  · exact natCast_ne_zero_of_lt (p := p) (n := 1) (by norm_num) (by omega)
      (by push_cast; linear_combination h - h')
  · exact natCast_ne_zero_of_lt (p := p) (n := 2) (by norm_num) (by omega)
      (by push_cast; linear_combination h - h')
  · exact natCast_ne_zero_of_lt (p := p) (n := 1) (by norm_num) (by omega)
      (by push_cast; linear_combination h' - x * h)
  · exact natCast_ne_zero_of_lt (p := p) (n := 2) (by norm_num) (by omega)
      (by push_cast; linear_combination h' - (x - 1) * h)
  · exact natCast_ne_zero_of_lt (p := p) (n := 3) (by norm_num) (by omega)
      (by push_cast; linear_combination h' - (x - 2) * h)
  · exact natCast_ne_zero_of_lt (p := p) (n := 1) (by norm_num) (by omega)
      (by push_cast; linear_combination h' - (x ^ 3 - x ^ 2) * h)

theorem cyc3_excl (hp5 : 5 ≤ p) (hq : 1 ≤ q) (h : p ∣ q ^ 2 + q + 1) :
    ¬ p ∣ q ∧ ¬ p ∣ q - 1 ∧ ¬ p ∣ q + 1 ∧ ¬ p ∣ q ^ 2 + 1 ∧ ¬ p ∣ q ^ 2 - q + 1 ∧
      ¬ p ∣ q ^ 4 - q ^ 2 + 1 := by
  obtain ⟨c1, c6, c12⟩ := cast_cyc (p := p) hq
  simp only [← ZMod.natCast_eq_zero_iff, c1, c6, c12] at h ⊢
  push_cast at h ⊢
  set x := (q : ZMod p)
  refine ⟨fun h' => ?_, fun h' => ?_, fun h' => ?_, fun h' => ?_, fun h' => ?_, fun h' => ?_⟩
  · exact natCast_ne_zero_of_lt (p := p) (n := 1) (by norm_num) (by omega)
      (by push_cast; linear_combination h - (x + 1) * h')
  · exact natCast_ne_zero_of_lt (p := p) (n := 3) (by norm_num) (by omega)
      (by push_cast; linear_combination h - (x + 2) * h')
  · exact natCast_ne_zero_of_lt (p := p) (n := 1) (by norm_num) (by omega)
      (by push_cast; linear_combination h - x * h')
  · exact natCast_ne_zero_of_lt (p := p) (n := 1) (by norm_num) (by omega)
      (by push_cast; linear_combination (1 + x) * h' - x * h)
  · exact natCast_ne_zero_of_lt (p := p) (n := 2) (by norm_num) (by omega)
      (by push_cast; linear_combination (1 - x) * h + (x + 1) * h')
  · exact natCast_ne_zero_of_lt (p := p) (n := 2) (by norm_num) (by omega)
      (by push_cast; linear_combination (x ^ 3 - x ^ 2 - x + 2) * h - x * h')

theorem cyc4_excl (hp5 : 5 ≤ p) (hq : 1 ≤ q) (h : p ∣ q ^ 2 + 1) :
    ¬ p ∣ q ∧ ¬ p ∣ q - 1 ∧ ¬ p ∣ q + 1 ∧ ¬ p ∣ q ^ 2 + q + 1 ∧ ¬ p ∣ q ^ 2 - q + 1 ∧
      ¬ p ∣ q ^ 4 - q ^ 2 + 1 := by
  obtain ⟨c1, c6, c12⟩ := cast_cyc (p := p) hq
  simp only [← ZMod.natCast_eq_zero_iff, c1, c6, c12] at h ⊢
  push_cast at h ⊢
  set x := (q : ZMod p)
  refine ⟨fun h' => ?_, fun h' => ?_, fun h' => ?_, fun h' => ?_, fun h' => ?_, fun h' => ?_⟩
  · exact natCast_ne_zero_of_lt (p := p) (n := 1) (by norm_num) (by omega)
      (by push_cast; linear_combination h - x * h')
  · exact natCast_ne_zero_of_lt (p := p) (n := 2) (by norm_num) (by omega)
      (by push_cast; linear_combination h - (x + 1) * h')
  · exact natCast_ne_zero_of_lt (p := p) (n := 2) (by norm_num) (by omega)
      (by push_cast; linear_combination h - (x - 1) * h')
  · exact natCast_ne_zero_of_lt (p := p) (n := 1) (by norm_num) (by omega)
      (by push_cast; linear_combination (1 + x) * h - x * h')
  · exact natCast_ne_zero_of_lt (p := p) (n := 1) (by norm_num) (by omega)
      (by push_cast; linear_combination (1 - x) * h + x * h')
  · exact natCast_ne_zero_of_lt (p := p) (n := 3) (by norm_num) (by omega)
      (by push_cast; linear_combination h' - (x ^ 2 - 2) * h)

theorem cyc6_excl (hp5 : 5 ≤ p) (hq : 1 ≤ q) (h : p ∣ q ^ 2 - q + 1) :
    ¬ p ∣ q ∧ ¬ p ∣ q - 1 ∧ ¬ p ∣ q + 1 ∧ ¬ p ∣ q ^ 2 + q + 1 ∧ ¬ p ∣ q ^ 2 + 1 ∧
      ¬ p ∣ q ^ 4 - q ^ 2 + 1 := by
  obtain ⟨c1, c6, c12⟩ := cast_cyc (p := p) hq
  simp only [← ZMod.natCast_eq_zero_iff, c1, c6, c12] at h ⊢
  push_cast at h ⊢
  set x := (q : ZMod p)
  refine ⟨fun h' => ?_, fun h' => ?_, fun h' => ?_, fun h' => ?_, fun h' => ?_, fun h' => ?_⟩
  · exact natCast_ne_zero_of_lt (p := p) (n := 1) (by norm_num) (by omega)
      (by push_cast; linear_combination h - (x - 1) * h')
  · exact natCast_ne_zero_of_lt (p := p) (n := 1) (by norm_num) (by omega)
      (by push_cast; linear_combination h - x * h')
  · exact natCast_ne_zero_of_lt (p := p) (n := 3) (by norm_num) (by omega)
      (by push_cast; linear_combination h - (x - 2) * h')
  · exact natCast_ne_zero_of_lt (p := p) (n := 2) (by norm_num) (by omega)
      (by push_cast; linear_combination (1 - x) * h' + (x + 1) * h)
  · exact natCast_ne_zero_of_lt (p := p) (n := 1) (by norm_num) (by omega)
      (by push_cast; linear_combination (1 - x) * h' + x * h)
  · exact natCast_ne_zero_of_lt (p := p) (n := 2) (by norm_num) (by omega)
      (by push_cast; linear_combination (2 + x - x ^ 2 - x ^ 3) * h + x * h')

end CFSG.OddStandard.GH71.S55.C5
