module

public import CFSG.Timmesfeld.Orders.ExceptionalWeylCert

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Timmesfeld.ExceptionalOrders

section Cast

variable {R : Type*} [CommRing R] (q : ℕ)

theorem geomSum_cast_nine (h : (q : R) ^ 2 + 1 = 0) : ((geomSum 9 1 q : ℕ) : R) = 1 := by
  simp only [geomSum, Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast
  linear_combination ((q : R) * ((q : R) + 1) * ((q : R) ^ 4 + 1)) * h

theorem geomSum_cast_three_four (h : (q : R) ^ 2 + 1 = 0) :
    ((geomSum 3 4 q : ℕ) : R) = 3 := by
  simp only [geomSum, Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast
  linear_combination (((q : R) ^ 2 - 1) * ((q : R) ^ 4 + 2)) * h

theorem geomSum_cast_two_five (h : (q : R) ^ 2 + 1 = 0) :
    ((geomSum 2 5 q : ℕ) : R) = 1 + q := by
  simp only [geomSum, Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast
  linear_combination ((q : R) * ((q : R) ^ 2 - 1)) * h

theorem geomSum_cast_two_nine (h : (q : R) ^ 2 + 1 = 0) :
    ((geomSum 2 9 q : ℕ) : R) = 1 + q := by
  simp only [geomSum, Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast
  linear_combination ((q : R) * ((q : R) ^ 2 - 1) * ((q : R) ^ 4 + 1)) * h

theorem geomSum_cast_fourteen (h : (q : R) ^ 2 + 1 = 0) :
    ((geomSum 14 1 q : ℕ) : R) = 1 + q := by
  simp only [geomSum, Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast
  linear_combination ((q : R) ^ 2 * ((q : R) + 1) * ((q : R) ^ 8 + (q : R) ^ 4 + 1)) * h

end Cast

theorem sq_add_one_eq_zero_zmod {p q : ℕ} (h : p ∣ q ^ 2 + 1) : (q : ZMod p) ^ 2 + 1 = 0 := by
  have := (ZMod.natCast_eq_zero_iff (q ^ 2 + 1) p).2 h
  simpa using this

theorem not_dvd_index_E6 {p q : ℕ} (hp : p.Prime) (h : p ∣ q ^ 2 + 1) :
    ¬ p ∣ geomSum 9 1 q * geomSum 3 4 q := by
  have : Fact p.Prime := ⟨hp⟩
  intro hd
  have hx := sq_add_one_eq_zero_zmod h
  have h3 : (3 : ZMod p) = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ p).2 hd
    push_cast at this
    rwa [geomSum_cast_nine q hx, geomSum_cast_three_four q hx, one_mul] at this
  have hp3 : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).1 (by exact_mod_cast h3)
  obtain rfl : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hp3
  revert hx
  generalize (q : ZMod 3) = x
  revert x
  decide

theorem not_dvd_index_E7 {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ∣ q ^ 2 + 1) :
    ¬ p ∣ geomSum 2 5 q * geomSum 2 9 q * geomSum 14 1 q := by
  have : Fact p.Prime := ⟨hp⟩
  intro hd
  have hx := sq_add_one_eq_zero_zmod h
  have h0 : (1 + (q : ZMod p)) ^ 3 = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ p).2 hd
    push_cast at this
    rw [geomSum_cast_two_five q hx, geomSum_cast_two_nine q hx,
      geomSum_cast_fourteen q hx] at this
    linear_combination this
  have h1 : 1 + (q : ZMod p) = 0 := pow_eq_zero_iff (by norm_num) |>.1 h0
  have h2 : (2 : ZMod p) = 0 := by
    linear_combination hx - ((q : ZMod p) - 1) * h1
  have hp2' : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 (by exact_mod_cast h2)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hp2')

end CFSG.LieType.SeitzGeneration
