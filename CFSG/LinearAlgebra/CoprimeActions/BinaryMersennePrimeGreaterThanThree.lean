module

import Mathlib.Tactic.NormNum.Pow

public import Mathlib.Data.Nat.Factors
public import CFSG.LinearAlgebra.CoprimeActions.BinaryMersennePrimePower
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.LinearAlgebra.CoprimeActions.BinaryMersennePrimeGreaterThanThree

theorem exists_prime_gt_three (e : ℕ) (he : 2 < e) :
    ∃ q : ℕ, q.Prime ∧ 3 < q ∧ q ∣ 2 ^ e - 1 := by
  by_contra hcon
  push Not at hcon
  have hpos : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  have h8 : 2 ^ e % 8 = 0 := by
    obtain ⟨t, rfl⟩ : ∃ t, e = t + 3 := ⟨e - 3, by omega⟩
    rw [pow_add]; simp
  have hbig : 2 ^ e ≥ 8 := by
    calc 2 ^ e ≥ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) he
      _ = 8 := by norm_num
  have hodd : ¬ 2 ∣ 2 ^ e - 1 := by omega
  have hne1 : 2 ^ e - 1 ≠ 1 := by omega
  have h3 : ∀ r : ℕ, r.Prime → r ∣ 2 ^ e - 1 → r = 3 := by
    intro r hr hrd
    have hle : r ≤ 3 := by
      by_contra h
      exact hcon r hr (by omega) hrd
    have h2 : r ≠ 2 := by
      rintro rfl; exact hodd hrd
    have := hr.two_le
    omega
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ e - 1 = 3 ^ k :=
    ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (n := 2 ^ e - 1) (p := 3)
      (by omega) (fun {d} hd hdd => h3 d hd hdd)⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne1 (by rw [hk]; simp)
  have hpp : IsPrimePow (2 ^ e - 1) := by
    rw [hk]; exact (Nat.prime_three.isPrimePow).pow hk0
  have hpr := (BinaryMersennePrimePower.prime_and_odd e he hpp).1
  have h3d : 3 ∣ 2 ^ e - 1 := by
    rw [hk]; exact dvd_pow_self 3 hk0
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hpr).1 h3d
  omega

end CFSG.LinearAlgebra.CoprimeActions.BinaryMersennePrimeGreaterThanThree
