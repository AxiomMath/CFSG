module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.LocalFourier

public section

open scoped BigOperators

namespace CFSG.LyonsUnitaryFour

@[expose] noncomputable def intPart (w : ℂ) : ℤ := by
  classical
  exact if h : ∃ n : ℤ, w = n then h.choose else 0

theorem intPart_spec {w : ℂ} (h : ∃ n : ℤ, w = n) : w = intPart w := by
  classical
  unfold intPart
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec

theorem intPart_intCast (n : ℤ) : intPart (n : ℂ) = n := by
  have h := intPart_spec (w := (n : ℂ)) ⟨n, rfl⟩
  exact_mod_cast h.symm

theorem intPart_eq_of_eq {w w' : ℂ} (h : w = w') : intPart w = intPart w' := by rw [h]

theorem fiveFourier_mod {X : Type*} [Monoid X] (f : X → ℂ) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5)
    (u v : X) (i : ℕ) : fiveFourier f ζ u v i = fiveFourier f ζ u v (i % 5) := by
  unfold fiveFourier
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have h1 : ∀ m, ζ ^ m = ζ ^ (m % 5) := fun m => by
    conv_lhs => rw [← Nat.mod_add_div m 5, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
  rw [h1 (4 * i * j), h1 (4 * (i % 5) * j)]
  congr 1
  exact (((Nat.mod_modEq i 5).symm.mul_left 4).mul_right j)

theorem fiveFourier_one {X : Type*} [Monoid X] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (u v : X)
    {i : ℕ} (hi : i < 5) : fiveFourier (fun _ => (1 : ℂ)) ζ u v i = if i = 0 then 1 else 0 := by
  unfold fiveFourier
  simp only [mul_one]
  rw [Finset.sum_congr rfl fun j _ => by rw [show 4 * i * j = (4 * i) * j from rfl],
    sum_range_five_pow_mul hζ]
  have hiff : 5 ∣ 4 * i ↔ i = 0 := by omega
  by_cases hi0 : i = 0
  · rw [ite_eq_left (hiff.mpr hi0), ite_eq_left hi0]
    norm_num
  · rw [ite_eq_right (fun h => hi0 (hiff.mp h)), ite_eq_right hi0, mul_zero]

end CFSG.LyonsUnitaryFour
