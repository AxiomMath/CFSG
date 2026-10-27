module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.LocalFourier

public section

open scoped BigOperators

namespace CFSG.LyonsUnitaryFour

theorem fiveFourier_inversion {X : Type*} [Monoid X] (f : X → ℂ) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ 5) (u v : X) {l : ℕ} (hl : l < 5) :
    f (u * v ^ l) = ∑ i ∈ Finset.range 5, fiveFourier f ζ u v i * ζ ^ (i * l) := by
  simp only [fiveFourier, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hinner : ∀ j ∈ Finset.range 5, ∑ i ∈ Finset.range 5,
      (5 : ℂ)⁻¹ * (ζ ^ (4 * i * j) * f (u * v ^ j)) * ζ ^ (i * l) =
      (5 : ℂ)⁻¹ * f (u * v ^ j) * ∑ i ∈ Finset.range 5, ζ ^ ((4 * j + l) * i) := by
    intro j _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (4 * j + l) * i = 4 * i * j + i * l by ring, pow_add]
    ring
  rw [Finset.sum_congr rfl hinner]
  simp only [sum_range_five_pow_mul hζ]
  have hiff : ∀ j ∈ Finset.range 5, (5 ∣ 4 * j + l ↔ j = l) := by
    intro j hj
    have := Finset.mem_range.mp hj
    omega
  rw [Finset.sum_congr rfl fun j hj => by rw [if_congr (hiff j hj) rfl rfl]]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_range, hl, ite_true]
  field_simp

end CFSG.LyonsUnitaryFour
