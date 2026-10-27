module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.HardMathSupport.Lang.E27Lie

private theorem dvd_of_zmod {n : ℕ} (h : ((n : ℕ) : ZMod 27) = 0) : 27 ∣ n :=
  (ZMod.natCast_eq_zero_iff n 27).1 h

theorem twentySeven_dvd_ordG2 (q : ℕ) : 27 ∣ q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · apply dvd_of_zmod
    have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq
    have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
    push_cast [Nat.cast_sub h6, Nat.cast_sub h2]
    generalize (q : ZMod 27) = x
    revert x
    decide

theorem twentySeven_dvd_ordPGL3 {q : ℕ} (hq : q % 3 = 1) :
    27 ∣ (q - 1) ^ 2 * q ^ 3 * ((q + 1) * (q ^ 2 + q + 1)) := by
  obtain ⟨t, rfl⟩ : ∃ t, q = 3 * t + 1 := ⟨q / 3, by omega⟩
  have h1 : 3 * t + 1 - 1 = 3 * t := by omega
  have h2 : (3 * t + 1) ^ 2 + (3 * t + 1) + 1 = 3 * (3 * t ^ 2 + 3 * t + 1) + 0 := by ring
  rw [h1]
  exact ⟨t ^ 2 * (3 * t + 1) ^ 3 * ((3 * t + 1 + 1) * (3 * t ^ 2 + 3 * t + 1)), by
    rw [h2]; ring⟩

theorem twentySeven_dvd_ordPGL3_even {q : ℕ} (hq : q % 3 = 1) :
    27 ∣ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) := by
  obtain ⟨t, rfl⟩ : ∃ t, q = 3 * t + 1 := ⟨q / 3, by omega⟩
  have h1 : (3 * t + 1) ^ 2 - 1 = 3 * (t * (3 * t + 2)) := by
    have : (3 * t + 1) ^ 2 = 3 * (t * (3 * t + 2)) + 1 := by ring
    omega
  have h2 : (3 * t + 1) ^ 3 - 1 = 9 * (t * (3 * t ^ 2 + 3 * t + 1)) := by
    have : (3 * t + 1) ^ 3 = 9 * (t * (3 * t ^ 2 + 3 * t + 1)) + 1 := by ring
    omega
  rw [h1, h2]
  exact ⟨(3 * t + 1) ^ 3 * (t * (3 * t + 2)) * (t * (3 * t ^ 2 + 3 * t + 1)), by ring⟩

theorem twentySeven_dvd_ordPGU3 {q : ℕ} (hq : q % 3 = 2) :
    27 ∣ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) := by
  obtain ⟨t, rfl⟩ : ∃ t, q = 3 * t + 2 := ⟨q / 3, by omega⟩
  have h1 : (3 * t + 2) ^ 2 - 1 = 3 * ((t + 1) * (3 * t + 1)) := by
    have : (3 * t + 2) ^ 2 = 3 * ((t + 1) * (3 * t + 1)) + 1 := by ring
    omega
  have h2 : (3 * t + 2) ^ 3 + 1 = 9 * ((t + 1) * (3 * t ^ 2 + 3 * t + 1)) := by ring
  rw [h1, h2]
  exact ⟨(3 * t + 2) ^ 3 * ((t + 1) * (3 * t + 1)) * ((t + 1) * (3 * t ^ 2 + 3 * t + 1)), by ring⟩

end CFSG.HardMathSupport.Lang.E27Lie
