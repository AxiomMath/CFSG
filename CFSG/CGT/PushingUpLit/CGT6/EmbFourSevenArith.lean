module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.CGT.PushingUpLit.CGT6

private theorem pos_of_sq_eq {S e m : ℕ} (hS : 0 < S) (hSe : S ^ 2 = m * e) : 0 < e := by
  rcases Nat.eq_zero_or_pos e with h | h
  · subst h
    have h0 : S ^ 2 = 0 := by simpa using hSe
    have := pow_eq_zero_iff (two_ne_zero) |>.mp h0
    omega
  · exact h

theorem weil_row_three {S a e j mC : ℕ} (hS : 0 < S) (haS : a ≤ S) (hSe : S ^ 2 = 3 ^ j * e)
    (hC1 : 1 ≤ mC) (hC : mC * 81 ≤ 3 ^ j) (hq : ((5 : ℤ) * a - S) ^ 2 ≤ 20 * e * mC) :
    7 ≤ S - a := by
  have he : 0 < e := pos_of_sq_eq hS hSe
  have h81 : 81 ≤ S ^ 2 := by
    calc 81 ≤ mC * 81 := Nat.le_mul_of_pos_left _ hC1
      _ ≤ 3 ^ j := hC
      _ ≤ 3 ^ j * e := Nat.le_mul_of_pos_right _ he
      _ = S ^ 2 := hSe.symm
  have hS9 : 9 ≤ S := by
    by_contra h
    have h' : S ≤ 8 := by omega
    nlinarith
  have hC' : (mC : ℤ) * 81 ≤ 3 ^ j := by exact_mod_cast hC
  have hSe' : (S : ℤ) ^ 2 = 3 ^ j * e := by exact_mod_cast hSe
  have h1 : (81 : ℤ) * ((5 : ℤ) * a - S) ^ 2 ≤ 20 * (S : ℤ) ^ 2 := by
    calc (81 : ℤ) * ((5 : ℤ) * a - S) ^ 2 ≤ 81 * (20 * e * mC) := by nlinarith
      _ = 20 * e * (mC * 81) := by ring
      _ ≤ 20 * e * 3 ^ j := by
        apply mul_le_mul_of_nonneg_left hC'
        positivity
      _ = 20 * (S : ℤ) ^ 2 := by rw [hSe']; ring
  have h2 : 9 * ((5 : ℤ) * a - S) < 5 * S := by
    by_contra h
    have h := not_lt.mp h
    have hSpos : (0 : ℤ) < S := by exact_mod_cast hS
    have h3 : (5 * (S : ℤ)) ^ 2 ≤ (9 * ((5 : ℤ) * a - S)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h 2
    nlinarith
  omega

theorem weil_row_five {S a e j mC : ℕ} (hS : 0 < S) (haS : a ≤ S) (hSe : S ^ 2 = 5 ^ j * e)
    (hC : mC * 5 ≤ 5 ^ j) (hq : ((5 : ℤ) * a - S) ^ 2 ≤ 20 * e * mC) :
    2 * S ≤ 5 * (S - a) := by
  have hC' : (mC : ℤ) * 5 ≤ 5 ^ j := by exact_mod_cast hC
  have hSe' : (S : ℤ) ^ 2 = 5 ^ j * e := by exact_mod_cast hSe
  have h1 : (5 : ℤ) * ((5 : ℤ) * a - S) ^ 2 ≤ 20 * (S : ℤ) ^ 2 := by
    calc (5 : ℤ) * ((5 : ℤ) * a - S) ^ 2 ≤ 5 * (20 * e * mC) := by nlinarith
      _ = 20 * e * (mC * 5) := by ring
      _ ≤ 20 * e * 5 ^ j := by
        apply mul_le_mul_of_nonneg_left hC'
        positivity
      _ = 20 * (S : ℤ) ^ 2 := by rw [hSe']; ring
  have h2 : (5 : ℤ) * a - S ≤ 2 * S := by
    by_contra h
    have h := not_le.mp h
    have hSpos : (0 : ℤ) < S := by exact_mod_cast hS
    have h3 : (2 * (S : ℤ)) ^ 2 ≤ ((5 : ℤ) * a - S) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h.le 2
    nlinarith
  omega

theorem weil_row_large {S a e j p mC : ℕ} (hp : 7 ≤ p) (hS : 0 < S) (haS : a ≤ S)
    (hSe : S ^ 2 = p ^ j * e) (hC1 : 1 ≤ mC) (hC : mC * p ^ 2 ≤ p ^ j)
    (hq : ((5 : ℤ) * a - S) ^ 2 ≤ 20 * e * mC) : 5 ≤ S - a := by
  have he : 0 < e := pos_of_sq_eq hS hSe
  have hpS : p ^ 2 ≤ S ^ 2 := by
    calc p ^ 2 ≤ mC * p ^ 2 := Nat.le_mul_of_pos_left _ hC1
      _ ≤ p ^ j := hC
      _ ≤ p ^ j * e := Nat.le_mul_of_pos_right _ he
      _ = S ^ 2 := hSe.symm
  have hS7 : 7 ≤ S := by
    have : p ≤ S := by
      by_contra h
      have h' : S < p := by omega
      nlinarith
    omega
  have hC' : (mC : ℤ) * p ^ 2 ≤ p ^ j := by exact_mod_cast hC
  have hSe' : (S : ℤ) ^ 2 = p ^ j * e := by exact_mod_cast hSe
  have h1 : (p : ℤ) ^ 2 * ((5 : ℤ) * a - S) ^ 2 ≤ 20 * (S : ℤ) ^ 2 := by
    calc (p : ℤ) ^ 2 * ((5 : ℤ) * a - S) ^ 2 ≤ (p : ℤ) ^ 2 * (20 * (e : ℤ) * (mC : ℤ)) := by
          apply mul_le_mul_of_nonneg_left hq
          positivity
      _ = 20 * (e : ℤ) * ((mC : ℤ) * (p : ℤ) ^ 2) := by ring
      _ ≤ 20 * (e : ℤ) * (p : ℤ) ^ j := by
        apply mul_le_mul_of_nonneg_left hC'
        positivity
      _ = 20 * (S : ℤ) ^ 2 := by rw [hSe']; ring
  have hSpos : (0 : ℤ) < S := by exact_mod_cast hS
  have hp7 : (7 : ℤ) ≤ p := by exact_mod_cast hp
  have h2 : (p : ℤ) * ((5 : ℤ) * a - S) < 5 * S := by
    by_contra h
    have h := not_lt.mp h
    have h3 : (5 * (S : ℤ)) ^ 2 ≤ ((p : ℤ) * ((5 : ℤ) * a - S)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h 2
    nlinarith
  by_cases ht : (5 : ℤ) * a - S ≤ 0
  · omega
  · have ht' : 0 < (5 : ℤ) * a - S := by omega
    have h4 : (7 : ℤ) * ((5 : ℤ) * a - S) ≤ (p : ℤ) * ((5 : ℤ) * a - S) :=
      mul_le_mul_of_nonneg_right hp7 ht'.le
    omega

theorem weil_arith {p j Mc Cc S a e : ℕ} (hp : p.Prime) (hodd : Odd p) (hj : 2 ≤ j)
    (hMc : Mc = p ^ j) (hC1 : 1 ≤ Cc) (hC : Cc * p ≤ Mc) (hC2 : p ≠ 5 → Cc * p ^ 2 ≤ Mc)
    (hC3 : p = 3 → Cc * 81 ≤ Mc) (hSe : S ^ 2 = Mc * e) (hS : 1 ≤ S) (haS : a ≤ S)
    (hq : (5 * (a : ℤ) - S) ^ 2 ≤ 20 * e * Cc) : (if p = 3 then 3 else 2) ≤ S - a := by
  subst hMc
  by_cases h3 : p = 3
  · subst h3
    have := weil_row_three hS haS hSe hC1 (hC3 rfl) hq
    simp only [↓reduceIte]
    omega
  · simp only [h3, ↓reduceIte]
    by_cases h5 : p = 5
    · subst h5
      have h := weil_row_five hS haS hSe hC hq
      have he : 0 < e := pos_of_sq_eq hS hSe
      have h25 : 25 ≤ S ^ 2 := by
        calc 25 = 5 ^ 2 := by norm_num
          _ ≤ 5 ^ j := Nat.pow_le_pow_right (by norm_num) hj
          _ ≤ 5 ^ j * e := Nat.le_mul_of_pos_right _ he
          _ = S ^ 2 := hSe.symm
      have : 5 ≤ S := by
        by_contra h'
        have h'' : S ≤ 4 := by omega
        nlinarith
      omega
    · have hp7 : 7 ≤ p := by
        have h2 := hp.two_le
        have hne2 : p ≠ 2 := by
          rintro rfl
          exact absurd hodd (by decide)
        have hne4 : p ≠ 4 := by
          rintro rfl
          exact absurd hp (by decide)
        have hne6 : p ≠ 6 := by
          rintro rfl
          exact absurd hp (by decide)
        omega
      have := weil_row_large hp7 hS haS hSe hC1 (hC2 h5) hq
      omega

end CFSG.CGT.PushingUpLit.CGT6
