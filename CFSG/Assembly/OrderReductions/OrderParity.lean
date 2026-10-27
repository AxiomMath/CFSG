module

public import CFSG.Open.OrderForm

public section

open CFSG.Open
open Finset

namespace CFSG.OrderReductions.OrderParity

theorem even_mul_div_of_dvd {first second divisor : ℕ} (even_first : Even first)
    (divides : divisor ∣ second) : Even (first * second / divisor) := by
  rw [Nat.mul_div_assoc first divides]
  exact even_first.mul_right _

theorem even_div_mul_of_dvd {first second divisor : ℕ} (even_second : Even second)
    (divides : divisor ∣ first) : Even (first * second / divisor) := by
  rw [Nat.mul_comm, Nat.mul_div_assoc second divides]
  exact even_second.mul_right _

theorem square_sub_one_factorization (order : ℕ) :
    order ^ 2 - 1 = (order - 1) * (order + 1) := by
  by_cases zero_order : order = 0
  · simp [zero_order]
  · have positive_order : 1 ≤ order := by omega
    have square_positive : 1 ≤ order ^ 2 := by nlinarith
    have subtraction := Nat.sub_add_cancel positive_order
    have square_subtraction := Nat.sub_add_cancel square_positive
    nlinarith

theorem even_power_of_even {order exponent : ℕ} (even_order : Even order)
    (positive_exponent : 0 < exponent) : Even (order ^ exponent) := by
  obtain ⟨depth, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : exponent ≠ 0)
  rw [pow_succ]
  exact even_order.mul_left _

theorem even_quotient_square_factor {order exponent remainder divisor : ℕ}
    (positive_exponent : 0 < exponent)
    (divides_minus : divisor ∣ order - 1) :
    Even (order ^ exponent * (order ^ 2 - 1) * remainder / divisor) := by
  rw [square_sub_one_factorization]
  rcases Nat.even_or_odd order with even_order | odd_order
  · have divides_factor : divisor ∣ (order - 1) * (order + 1) * remainder :=
      dvd_mul_of_dvd_left (dvd_mul_of_dvd_left divides_minus _) _
    rw [mul_assoc]
    exact even_mul_div_of_dvd (even_power_of_even even_order positive_exponent) divides_factor
  · have even_plus : Even (order + 1) := by
      obtain ⟨half, order_eq⟩ := odd_order
      exact ⟨half + 1, by omega⟩
    have even_remaining : Even (order ^ exponent * (order + 1) * remainder) :=
      (even_plus.mul_left _).mul_right _
    have product_eq : order ^ exponent * ((order - 1) * (order + 1)) * remainder =
        (order - 1) * (order ^ exponent * (order + 1) * remainder) := by ring
    rw [product_eq]
    exact even_div_mul_of_dvd even_remaining divides_minus

theorem even_quotient_square_factor_plus {order exponent remainder divisor : ℕ}
    (positive_exponent : 0 < exponent)
    (divides_plus : divisor ∣ order + 1) :
    Even (order ^ exponent * (order ^ 2 - 1) * remainder / divisor) := by
  rw [square_sub_one_factorization]
  rcases Nat.even_or_odd order with even_order | odd_order
  · have divides_factor : divisor ∣ (order - 1) * (order + 1) * remainder :=
      dvd_mul_of_dvd_left (dvd_mul_of_dvd_right divides_plus _) _
    rw [mul_assoc]
    exact even_mul_div_of_dvd (even_power_of_even even_order positive_exponent) divides_factor
  · have even_minus : Even (order - 1) := by
      obtain ⟨half, order_eq⟩ := odd_order
      exact ⟨half, by omega⟩
    have even_remaining : Even (order ^ exponent * (order - 1) * remainder) :=
      (even_minus.mul_left _).mul_right _
    have product_eq : order ^ exponent * ((order - 1) * (order + 1)) * remainder =
        (order + 1) * (order ^ exponent * (order - 1) * remainder) := by ring
    rw [product_eq]
    exact even_div_mul_of_dvd even_remaining divides_plus

theorem orderA_even (rank order : ℕ) (positive_rank : 1 ≤ rank) : Even (orderA rank order) := by
  have member_two : 2 ∈ Icc 2 (rank + 1) := by simp; omega
  rw [orderA, Finset.prod_eq_mul_prod_sdiff_singleton_of_mem member_two, ← mul_assoc]
  apply even_quotient_square_factor
  · have product_lower : 2 ≤ rank * (rank + 1) := by nlinarith
    omega
  · exact Nat.gcd_dvd_right _ _

theorem orderTwistedA_even (rank order : ℕ) (rank_lower : 2 ≤ rank) :
    Even (orderTwistedA rank order) := by
  have member_two : 2 ∈ Icc 2 (rank + 1) := by simp; omega
  rw [orderTwistedA, Finset.prod_eq_mul_prod_sdiff_singleton_of_mem member_two, ← mul_assoc]
  simp only [show Even (2 : ℕ) from by decide, ↓reduceIte]
  apply even_quotient_square_factor_plus
  · have product_lower : 2 ≤ rank * (rank + 1) := by nlinarith
    omega
  · exact Nat.gcd_dvd_right _ _

theorem orderBC_even (rank order : ℕ) (rank_lower : 2 ≤ rank) : Even (orderBC rank order) := by
  have member_one : 1 ∈ Icc 1 rank := by simp; omega
  rw [orderBC, Finset.prod_eq_mul_prod_sdiff_singleton_of_mem member_one, ← mul_assoc]
  simp only [mul_one]
  apply even_quotient_square_factor
  · nlinarith
  · exact Nat.gcd_dvd_right _ _

theorem eight_dvd_square_sub_one_of_odd {order : ℕ} (odd_order : Odd order) :
    8 ∣ order ^ 2 - 1 := by
  obtain ⟨half, order_eq⟩ := odd_order
  obtain ⟨quarter, product_eq⟩ := Nat.even_mul_succ_self half
  have positive_square : 1 ≤ order ^ 2 := by nlinarith
  have subtraction := Nat.sub_add_cancel positive_square
  refine ⟨quarter, ?_⟩
  nlinarith

theorem eight_dvd_power_times_square_sub_one {order exponent : ℕ}
    (exponent_lower : 3 ≤ exponent) : 8 ∣ order ^ exponent * (order ^ 2 - 1) := by
  rcases Nat.even_or_odd order with even_order | odd_order
  · have two_divides : 2 ∣ order := even_iff_two_dvd.mp even_order
    have eight_divides : 8 ∣ order ^ exponent := by
      have first : 2 ^ 3 ∣ order ^ 3 := pow_dvd_pow_of_dvd two_divides 3
      exact first.trans (pow_dvd_pow order exponent_lower)
    exact dvd_mul_of_dvd_left eight_divides _
  · exact dvd_mul_of_dvd_right (eight_dvd_square_sub_one_of_odd odd_order) _

theorem even_divisor_of_eight_dvd {numerator divisor : ℕ}
    (divides_four : divisor ∣ 4) (divides_eight : 8 ∣ numerator) :
    Even (numerator / divisor) := by
  have divisor_divides : divisor ∣ numerator :=
    divides_four.trans ((by decide : 4 ∣ 8).trans divides_eight)
  apply even_iff_two_dvd.mpr
  apply (Nat.dvd_div_iff_mul_dvd divisor_divides).mpr
  simpa only [Nat.mul_comm divisor 2] using
    (mul_dvd_mul_left 2 divides_four).trans divides_eight

theorem orderD_even (rank order : ℕ) (rank_lower : 4 ≤ rank) : Even (orderD rank order) := by
  have member_one : 1 ∈ Icc 1 (rank - 1) := by simp; omega
  rw [orderD, Finset.prod_eq_mul_prod_sdiff_singleton_of_mem member_one]
  simp only [mul_one]
  apply even_divisor_of_eight_dvd (Nat.gcd_dvd_left _ _)
  have exponent_lower : 3 ≤ rank * (rank - 1) := by
    have subtraction := Nat.sub_add_cancel (show 1 ≤ rank from by omega)
    nlinarith
  have divides := eight_dvd_power_times_square_sub_one (order := order) exponent_lower
  have product_eq : order ^ (rank * (rank - 1)) * (order ^ rank - 1) *
      ((order ^ 2 - 1) * ∏ index ∈ Icc 1 (rank - 1) \ {1}, (order ^ (2 * index) - 1)) =
      (order ^ (rank * (rank - 1)) * (order ^ 2 - 1)) *
      ((order ^ rank - 1) * ∏ index ∈ Icc 1 (rank - 1) \ {1}, (order ^ (2 * index) - 1)) := by ring
  rw [product_eq]
  exact dvd_mul_of_dvd_left divides _

theorem orderTwistedD_even (rank order : ℕ) (rank_lower : 4 ≤ rank) :
    Even (orderTwistedD rank order) := by
  have member_one : 1 ∈ Icc 1 (rank - 1) := by simp; omega
  rw [orderTwistedD, Finset.prod_eq_mul_prod_sdiff_singleton_of_mem member_one]
  simp only [mul_one]
  apply even_divisor_of_eight_dvd (Nat.gcd_dvd_left _ _)
  have exponent_lower : 3 ≤ rank * (rank - 1) := by
    have subtraction := Nat.sub_add_cancel (show 1 ≤ rank from by omega)
    nlinarith
  have divides := eight_dvd_power_times_square_sub_one (order := order) exponent_lower
  have product_eq : order ^ (rank * (rank - 1)) * (order ^ rank + 1) *
      ((order ^ 2 - 1) * ∏ index ∈ Icc 1 (rank - 1) \ {1}, (order ^ (2 * index) - 1)) =
      (order ^ (rank * (rank - 1)) * (order ^ 2 - 1)) *
      ((order ^ rank + 1) * ∏ index ∈ Icc 1 (rank - 1) \ {1}, (order ^ (2 * index) - 1)) := by ring
  rw [product_eq]
  exact dvd_mul_of_dvd_left divides _

theorem orderE6_even (order : ℕ) : Even (orderE6 order) := by
  have product_eq : order ^ 36 * (order ^ 12 - 1) * (order ^ 9 - 1) * (order ^ 8 - 1) *
      (order ^ 6 - 1) * (order ^ 5 - 1) * (order ^ 2 - 1) =
      order ^ 36 * (order ^ 2 - 1) *
      ((order ^ 12 - 1) * (order ^ 9 - 1) * (order ^ 8 - 1) * (order ^ 6 - 1) *
        (order ^ 5 - 1)) := by ring
  rw [orderE6, product_eq]
  exact even_quotient_square_factor (by decide) (Nat.gcd_dvd_right _ _)

theorem orderTwistedE6_even (order : ℕ) : Even (orderTwistedE6 order) := by
  have product_eq : order ^ 36 * (order ^ 12 - 1) * (order ^ 9 + 1) * (order ^ 8 - 1) *
      (order ^ 6 - 1) * (order ^ 5 + 1) * (order ^ 2 - 1) =
      order ^ 36 * (order ^ 2 - 1) *
      ((order ^ 12 - 1) * (order ^ 9 + 1) * (order ^ 8 - 1) * (order ^ 6 - 1) *
        (order ^ 5 + 1)) := by ring
  rw [orderTwistedE6, product_eq]
  exact even_quotient_square_factor_plus (by decide) (Nat.gcd_dvd_right _ _)

theorem orderE7_even (order : ℕ) : Even (orderE7 order) := by
  have product_eq : order ^ 63 * (order ^ 18 - 1) * (order ^ 14 - 1) * (order ^ 12 - 1) *
      (order ^ 10 - 1) * (order ^ 8 - 1) * (order ^ 6 - 1) * (order ^ 2 - 1) =
      order ^ 63 * (order ^ 2 - 1) *
      ((order ^ 18 - 1) * (order ^ 14 - 1) * (order ^ 12 - 1) * (order ^ 10 - 1) *
        (order ^ 8 - 1) * (order ^ 6 - 1)) := by ring
  rw [orderE7, product_eq]
  exact even_quotient_square_factor (by decide) (Nat.gcd_dvd_right _ _)

theorem even_power_times_square_sub_one {order exponent : ℕ} (positive_exponent : 0 < exponent) :
    Even (order ^ exponent * (order ^ 2 - 1)) := by
  have conclusion := even_quotient_square_factor (order := order) (remainder := 1)
    (divisor := 1) positive_exponent (one_dvd _)
  simpa only [mul_one, Nat.div_one] using conclusion

theorem orderE8_even (order : ℕ) : Even (orderE8 order) := by
  have product_eq : orderE8 order = order ^ 120 * (order ^ 2 - 1) *
      ((order ^ 30 - 1) * (order ^ 24 - 1) * (order ^ 20 - 1) * (order ^ 18 - 1) *
        (order ^ 14 - 1) * (order ^ 12 - 1) * (order ^ 8 - 1)) := by unfold orderE8; ring
  rw [product_eq]
  exact (even_power_times_square_sub_one (by decide)).mul_right _

theorem orderF4_even (order : ℕ) : Even (orderF4 order) := by
  have product_eq : orderF4 order = order ^ 24 * (order ^ 2 - 1) *
      ((order ^ 12 - 1) * (order ^ 8 - 1) * (order ^ 6 - 1)) := by unfold orderF4; ring
  rw [product_eq]
  exact (even_power_times_square_sub_one (by decide)).mul_right _

theorem orderG2_even (order : ℕ) : Even (orderG2 order) := by
  have product_eq : orderG2 order = order ^ 6 * (order ^ 2 - 1) * (order ^ 6 - 1) := by
    unfold orderG2
    ring
  rw [product_eq]
  exact (even_power_times_square_sub_one (by decide)).mul_right _

theorem orderTrialityD4_even (order : ℕ) : Even (orderTrialityD4 order) := by
  have product_eq : orderTrialityD4 order = order ^ 12 * (order ^ 2 - 1) *
      ((order ^ 8 + order ^ 4 + 1) * (order ^ 6 - 1)) := by unfold orderTrialityD4; ring
  rw [product_eq]
  exact (even_power_times_square_sub_one (by decide)).mul_right _

end CFSG.OrderReductions.OrderParity
