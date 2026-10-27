module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

theorem u3two_padic_of_odd {n : ℕ} (h : Odd n) : padicValNat 2 n = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  intro h2
  obtain ⟨m, rfl⟩ := h
  omega

theorem u3two_padic_cube_add_one (q : ℕ) (hq : Odd q) :
    padicValNat 2 (q ^ 3 + 1) = padicValNat 2 (q + 1) := by
  obtain ⟨k, rfl⟩ := hq
  have e : (2 * k + 1) ^ 3 + 1 = (2 * k + 1 + 1) * (4 * k ^ 2 + 2 * k + 1) := by ring
  have hodd : Odd (4 * k ^ 2 + 2 * k + 1) := ⟨2 * k ^ 2 + k, by ring⟩
  rw [e, padicValNat.mul (by omega) (by positivity), u3two_padic_of_odd hodd, add_zero]

theorem u3two_padic_sq_sub_one (q : ℕ) (hq : Odd q) (h1 : 1 < q) :
    padicValNat 2 (q ^ 2 - 1) = padicValNat 2 (q - 1) + padicValNat 2 (q + 1) := by
  obtain ⟨k, rfl⟩ := hq
  have hk : 1 ≤ k := by omega
  have e1 : (2 * k + 1) ^ 2 - 1 = 2 * k * (2 * k + 1 + 1) := by
    have : (2 * k + 1) ^ 2 = 2 * k * (2 * k + 1 + 1) + 1 := by ring
    omega
  have e2 : 2 * k + 1 - 1 = 2 * k := by omega
  rw [e1, e2, padicValNat.mul (by omega) (by omega)]

theorem u3two_padic_add_one_of_mod4_one (q : ℕ) (h : q % 4 = 1) :
    padicValNat 2 (q + 1) = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, q = 4 * m + 1 := ⟨q / 4, by omega⟩
  have e : 4 * m + 1 + 1 = 2 * (2 * m + 1) := by ring
  have hodd : Odd (2 * m + 1) := ⟨m, rfl⟩
  rw [e, padicValNat.mul (by norm_num) (by omega), u3two_padic_of_odd hodd, padicValNat_self]

theorem u3two_padic_sub_one_of_mod4_three (q : ℕ) (h : q % 4 = 3) :
    padicValNat 2 (q - 1) = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, q = 4 * m + 3 := ⟨q / 4, by omega⟩
  have e : 4 * m + 3 - 1 = 2 * (2 * m + 1) := by omega
  have hodd : Odd (2 * m + 1) := ⟨m, rfl⟩
  rw [e, padicValNat.mul (by norm_num) (by omega), u3two_padic_of_odd hodd, padicValNat_self]

theorem u3two_padic_order (q : ℕ) (hq : Odd q) (h1 : 1 < q) :
    padicValNat 2 (q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1)) =
      padicValNat 2 (q - 1) + 2 * padicValNat 2 (q + 1) := by
  have hq2 : 1 < q ^ 2 := by nlinarith
  have hq3 : q ^ 3 ≠ 0 := pow_ne_zero 3 (by omega)
  have hsub : q ^ 2 - 1 ≠ 0 := by omega
  have hadd : q ^ 3 + 1 ≠ 0 := by omega
  have hodd3 : Odd (q ^ 3) := hq.pow
  rw [padicValNat.mul (mul_ne_zero hq3 hsub) hadd, padicValNat.mul hq3 hsub,
    u3two_padic_of_odd hodd3, u3two_padic_sq_sub_one q hq h1,
    u3two_padic_cube_add_one q hq]
  omega

end CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

end
