module

public import CFSG.Open.OrderForm

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4XN

open CFSG.Open

theorem orderA_one_eq (n : ℕ) : orderA 1 n = n * (n ^ 2 - 1) / Nat.gcd 2 (n - 1) := by
  simp [orderA]

theorem orderA_two_eq (n : ℕ) :
    orderA 2 n = n ^ 3 * ((n ^ 2 - 1) * (n ^ 3 - 1)) / Nat.gcd 3 (n - 1) := by
  have hI : Finset.Icc 2 3 = {2, 3} := by decide
  simp [orderA, hI, Finset.prod_pair]

theorem orderTwistedA_two_eq (n : ℕ) :
    orderTwistedA 2 n = n ^ 3 * ((n ^ 2 - 1) * (n ^ 3 + 1)) / Nat.gcd 3 (n + 1) := by
  have hI : Finset.Icc 2 3 = {2, 3} := by decide
  simp [orderTwistedA, hI, Finset.prod_pair, Nat.even_iff]

theorem A1_ne (n : ℕ) (hn : n % 2 = 0) (h2 : 2 ≤ n) : orderA 1 n ≠ 174182400 := by
  intro h
  rw [orderA_one_eq] at h
  have hg : Nat.gcd 2 (n - 1) = 1 := by
    rw [Nat.gcd_rec]
    have h1 : (n - 1) % 2 = 1 := by omega
    rw [h1]
    rfl
  rw [hg, Nat.div_one] at h
  by_cases hbig : 561 ≤ n
  · have h1 : 561 ^ 2 - 1 ≤ n ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hbig 2) 1
    have hprod := Nat.mul_le_mul hbig h1
    rw [h] at hprod
    norm_num at hprod
  · have hlt : n < 561 := by omega
    have key : ∀ n < 561, n % 2 = 0 → n * (n ^ 2 - 1) ≠ 174182400 := by decide +kernel
    exact key n hlt hn h

theorem A2_ne (n : ℕ) (h9 : n % 9 = 4 ∨ n % 9 = 7) : orderA 2 n ≠ 174182400 := by
  intro h
  rw [orderA_two_eq, Nat.gcd_eq_left (show 3 ∣ n - 1 by omega)] at h
  by_cases hbig : 13 ≤ n
  · have h1 : 13 ^ 2 - 1 ≤ n ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hbig 2) 1
    have h2' : 13 ^ 3 - 1 ≤ n ^ 3 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hbig 3) 1
    have h3 : 13 ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left hbig 3
    have hprod := Nat.mul_le_mul h3 (Nat.mul_le_mul h1 h2')
    generalize n ^ 3 * ((n ^ 2 - 1) * (n ^ 3 - 1)) = X at h hprod
    norm_num at hprod
    omega
  · have hlt : n < 13 := by omega
    have key : ∀ n < 13, (n % 9 = 4 ∨ n % 9 = 7) →
        n ^ 3 * ((n ^ 2 - 1) * (n ^ 3 - 1)) / 3 ≠ 174182400 := by decide +kernel
    exact key n hlt h9 h

theorem TA2_ne (n : ℕ) (h9 : n % 9 = 2 ∨ n % 9 = 5) : orderTwistedA 2 n ≠ 174182400 := by
  intro h
  rw [orderTwistedA_two_eq, Nat.gcd_eq_left (show 3 ∣ n + 1 by omega)] at h
  by_cases hbig : 13 ≤ n
  · have h1 : 13 ^ 2 - 1 ≤ n ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hbig 2) 1
    have h2' : 13 ^ 3 + 1 ≤ n ^ 3 + 1 := Nat.add_le_add_right (Nat.pow_le_pow_left hbig 3) 1
    have h3 : 13 ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left hbig 3
    have hprod := Nat.mul_le_mul h3 (Nat.mul_le_mul h1 h2')
    generalize n ^ 3 * ((n ^ 2 - 1) * (n ^ 3 + 1)) = X at h hprod
    norm_num at hprod
    omega
  · have hlt : n < 13 := by omega
    have key : ∀ n < 13, (n % 9 = 2 ∨ n % 9 = 5) →
        n ^ 3 * ((n ^ 2 - 1) * (n ^ 3 + 1)) / 3 ≠ 174182400 := by decide +kernel
    exact key n hlt h9 h

end CFSG.LocalAnalysis.GLTheoremA.D4XN
