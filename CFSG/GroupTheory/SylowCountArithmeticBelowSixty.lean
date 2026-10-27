module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.GroupTheory

theorem sylow_count_arithmetic_below_sixty (m : ℕ) (hm2 : 2 ≤ m) (hm60 : m < 60)
    (h : ∀ p a b : ℕ, p.Prime → p ∣ m → 1 ≤ a → ¬ p ∣ b → m = p ^ a * b →
      ∃ d : ℕ, 5 ≤ d ∧ d ∣ b ∧ d ≡ 1 [MOD p]) :
    m = 30 ∨ m = 56 := by
  interval_cases m
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 2 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 1 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 3 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 1 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 2 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 1 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 5 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 1 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 2 1 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 3 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 7 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 1 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 2 3 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 1 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 3 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 1 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 5 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 2 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 11 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 1 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 2 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 3 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 13 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 1 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 7 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 2 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, hd1⟩ :=
      h 3 1 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 5 := Nat.le_of_dvd (by norm_num) hdb
    have hd : d = 5 := le_antisymm hdle hd5
    subst hd
    revert hdb hd1
    decide
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 2 4 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 1 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 17 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 1 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 3 2 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 2 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 19 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 1 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 5 1 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 4 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 7 1 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 3 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 11 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 2 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 23 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 1 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 2 3 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 3 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 5 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 1 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 13 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 2 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 3 3 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 1 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 7 1 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 4 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 29 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 1 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · left; rfl
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 31 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 1 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 2 5 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 1 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, hd1⟩ :=
      h 3 1 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 11 := Nat.le_of_dvd (by norm_num) hdb
    interval_cases d <;> revert hdb hd1 <;> decide
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 17 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 2 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, hd1⟩ :=
      h 5 1 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 7 := Nat.le_of_dvd (by norm_num) hdb
    interval_cases d <;> revert hdb hd1 <;> decide
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 3 2 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 4 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 37 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 1 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 19 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 2 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 13 1 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 3 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, hd1⟩ :=
      h 5 1 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 8 := Nat.le_of_dvd (by norm_num) hdb
    interval_cases d <;> revert hdb hd1 <;> decide
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 41 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 1 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, hd1⟩ :=
      h 7 1 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 6 := Nat.le_of_dvd (by norm_num) hdb
    interval_cases d <;> revert hdb hd1 <;> decide
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 43 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 1 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 11 1 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 4 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, hd1⟩ :=
      h 3 2 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 5 := Nat.le_of_dvd (by norm_num) hdb
    have hd : d = 5 := le_antisymm hdle hd5
    subst hd
    revert hdb hd1
    decide
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 23 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 2 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 47 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 1 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 2 4 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 3 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 7 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 1 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 5 2 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 2 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, hd1⟩ :=
      h 3 1 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 17 := Nat.le_of_dvd (by norm_num) hdb
    interval_cases d <;> revert hdb hd1 <;> decide
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 13 1 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 4 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 53 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 1 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 3 3 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 2 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, hd1⟩ :=
      h 11 1 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 5 := Nat.le_of_dvd (by norm_num) hdb
    have hd : d = 5 := le_antisymm hdle hd5
    subst hd
    revert hdb hd1
    decide
  · right; rfl
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 19 1 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 3 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 29 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 2 := Nat.le_of_dvd (by norm_num) hdb
    omega
  · exfalso
    obtain ⟨d, hd5, hdb, -⟩ :=
      h 59 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hdle : d ≤ 1 := Nat.le_of_dvd (by norm_num) hdb
    omega

end CFSG.GroupTheory
