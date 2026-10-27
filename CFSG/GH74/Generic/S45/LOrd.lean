module

public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.GH74.Generic.S45

@[expose] def OrdClosable (c : ℕ) : Prop :=
  ∀ q : ℕ, 5 ≤ q → (q % 8 = 3 ∨ q % 8 = 5) → ¬ (q * (q ^ 2 - 1) / 2 ∣ c)

theorem q_le_of_div_le {c B q : ℕ} (hB : 2 * c + 1 < (B + 1) * ((B + 1) ^ 2 - 1))
    (h : q * (q ^ 2 - 1) / 2 ≤ c) : q ≤ B := by
  by_contra hgt
  push Not at hgt
  have h1 : (B + 1) ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hgt 2
  have h2 : (B + 1) * ((B + 1) ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
    Nat.mul_le_mul hgt (Nat.sub_le_sub_right h1 1)
  omega

theorem ordClosable_48 : OrdClosable 48 := by
  intro q hq5 hq8 hdvd
  have hle : q * (q ^ 2 - 1) / 2 ≤ 48 := Nat.le_of_dvd (by norm_num) hdvd
  have hq : q ≤ 6 := q_le_of_div_le (B := 6) (by norm_num) hle
  interval_cases q <;> omega

theorem ordClosable_384 : OrdClosable 384 := by
  intro q hq5 hq8 hdvd
  have hle : q * (q ^ 2 - 1) / 2 ≤ 384 := Nat.le_of_dvd (by norm_num) hdvd
  have hq : q ≤ 9 := q_le_of_div_le (B := 9) (by norm_num) hle
  interval_cases q <;> omega

theorem ordClosable_320 : OrdClosable 320 := by
  intro q hq5 hq8 hdvd
  have hle : q * (q ^ 2 - 1) / 2 ≤ 320 := Nat.le_of_dvd (by norm_num) hdvd
  have hq : q ≤ 8 := q_le_of_div_le (B := 8) (by norm_num) hle
  interval_cases q <;> omega

theorem ordClosable_1344 : OrdClosable 1344 := by
  intro q hq5 hq8 hdvd
  have hle : q * (q ^ 2 - 1) / 2 ≤ 1344 := Nat.le_of_dvd (by norm_num) hdvd
  have hq : q ≤ 14 := q_le_of_div_le (B := 14) (by norm_num) hle
  interval_cases q <;> omega

theorem ordClosable_2688 : OrdClosable 2688 := by
  intro q hq5 hq8 hdvd
  have hle : q * (q ^ 2 - 1) / 2 ≤ 2688 := Nat.le_of_dvd (by norm_num) hdvd
  have hq : q ≤ 18 := q_le_of_div_le (B := 18) (by norm_num) hle
  interval_cases q <;> omega

theorem ordClosable_2448 : OrdClosable 2448 := by
  intro q hq5 hq8 hdvd
  have hle : q * (q ^ 2 - 1) / 2 ≤ 2448 := Nat.le_of_dvd (by norm_num) hdvd
  have hq : q ≤ 17 := q_le_of_div_le (B := 17) (by norm_num) hle
  interval_cases q <;> omega

theorem ordClosable_12096 : OrdClosable 12096 := by
  intro q hq5 hq8 hdvd
  have hle : q * (q ^ 2 - 1) / 2 ≤ 12096 := Nat.le_of_dvd (by norm_num) hdvd
  have hq : q ≤ 28 := q_le_of_div_le (B := 28) (by norm_num) hle
  interval_cases q <;> omega

end CFSG.GH74.Generic.S45
