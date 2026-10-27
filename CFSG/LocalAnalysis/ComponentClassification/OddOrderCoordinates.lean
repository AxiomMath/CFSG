module

public import CFSG.Assembly.Defs

public section

namespace CFSG.ComponentClassification.OddOrderCoordinates

theorem one_of_two_power {G : Type*} [Group G] (member : G)
    (exponent : ℕ) (hpower : member ^ (2 ^ exponent) = 1) (hodd : Odd (orderOf member)) : member = 1 := by
  obtain ⟨power, _, horder⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hpower)
  cases power with
  | zero => exact orderOf_eq_one_iff.mp (by simpa only [pow_zero] using horder)
  | succ power =>
      have hdivides : 2 ∣ orderOf member := by
        rw [horder, pow_succ]
        exact dvd_mul_left 2 (2 ^ power)
      exact (hodd.not_two_dvd_nat hdivides).elim

theorem equal_two_power {G H : Type*} [Group G] [Group H] (homomorphism : G →* H)
    (first second : G) (firstExponent secondExponent : ℕ)
    (hfirst : first ^ (2 ^ firstExponent) = 1) (hsecond : second ^ (2 ^ secondExponent) = 1)
    (hodd : Odd (orderOf (first⁻¹ * second))) :
    homomorphism first = 1 ↔ homomorphism second = 1 := by
  have himageOdd := hodd.of_dvd_nat (orderOf_map_dvd homomorphism (first⁻¹ * second))
  constructor
  · intro hfirstImage
    have hsecondOdd : Odd (orderOf (homomorphism second)) := by
      simpa only [map_mul, map_inv, hfirstImage, inv_one, one_mul] using himageOdd
    apply one_of_two_power _ secondExponent _ hsecondOdd
    rw [← map_pow, hsecond, map_one]
  · intro hsecondImage
    have hfirstOdd : Odd (orderOf ((homomorphism first)⁻¹)) := by
      simpa only [map_mul, map_inv, hsecondImage, mul_one] using himageOdd
    apply inv_eq_one.mp
    apply one_of_two_power _ firstExponent _ hfirstOdd
    rw [inv_pow, ← map_pow, hfirst, map_one, inv_one]

theorem equal {G H : Type*} [Group G] [Group H] (homomorphism : G →* H)
    (first second : G) (hfirst : first ^ 2 = 1) (hsecond : second ^ 2 = 1)
    (hodd : Odd (orderOf (first⁻¹ * second))) :
    homomorphism first = 1 ↔ homomorphism second = 1 := by
  have himageOdd : Odd (orderOf (homomorphism (first⁻¹ * second))) :=
    hodd.of_dvd_nat (orderOf_map_dvd homomorphism _)
  constructor
  · intro hfirstImage
    have hsecondOdd : Odd (orderOf (homomorphism second)) := by
      simpa only [map_mul, map_inv, hfirstImage, inv_one, one_mul] using himageOdd
    have hsecondSquare : homomorphism second ^ 2 = 1 := by
      rw [← map_pow, hsecond, map_one]
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hsecondSquare) with hone | htwo
    · exact orderOf_eq_one_iff.mp hone
    · exact (hsecondOdd.not_two_dvd_nat (htwo ▸ dvd_rfl)).elim
  · intro hsecondImage
    have hfirstOdd : Odd (orderOf ((homomorphism first)⁻¹)) := by
      simpa only [map_mul, map_inv, hsecondImage, mul_one] using himageOdd
    have hfirstSquare : (homomorphism first)⁻¹ ^ 2 = 1 := by
      rw [inv_pow, ← map_pow, hfirst, map_one, inv_one]
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hfirstSquare) with hone | htwo
    · exact inv_eq_one.mp (orderOf_eq_one_iff.mp hone)
    · exact (hfirstOdd.not_two_dvd_nat (htwo ▸ dvd_rfl)).elim

end CFSG.ComponentClassification.OddOrderCoordinates
