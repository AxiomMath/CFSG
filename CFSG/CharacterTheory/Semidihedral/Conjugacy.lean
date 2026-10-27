module

public import CFSG.CharacterTheory.Semidihedral.ElementOrders
import CFSG.CharacterTheory.Semidihedral.DerivedAndIndexTwo

public section

namespace CFSG.Semidihedral

open CFSG.Open

theorem element_reflection_inv (n : ℕ) (hn : 3 ≤ n) (i : ZMod (modulus n)) :
    (element n hn i 1)⁻¹ = element n hn (-twist n * i) 1 := by
  apply inv_eq_of_mul_eq_one_right
  rw [element_reflection_mul, show (1 + 1 : ZMod 2) = 0 by decide]
  have hzero : i + twist n * (-twist n * i) = 0 := by
    calc
      i + twist n * (-twist n * i) = i - twist n ^ 2 * i := by ring
      _ = 0 := by rw [twist_sq hn]; ring
  rw [hzero, element_zero_zero]

theorem conjugate_rotation_by_rotation (n : ℕ) (hn : 3 ≤ n)
    (i j : ZMod (modulus n)) :
    element n hn j 0 * element n hn i 0 * (element n hn j 0)⁻¹ =
      element n hn i 0 := by
  rw [element_rotation_inv, element_rotation_mul, element_rotation_mul]
  congr 1
  ring

theorem conjugate_rotation_by_reflection (n : ℕ) (hn : 3 ≤ n)
    (i j : ZMod (modulus n)) :
    element n hn j 1 * element n hn i 0 * (element n hn j 1)⁻¹ =
      element n hn (twist n * i) 0 := by
  rw [element_reflection_inv, element_reflection_mul, add_zero,
    element_reflection_mul, show (1 + 1 : ZMod 2) = 0 by decide]
  congr 1
  calc
    j + twist n * i + twist n * (-twist n * j) =
        twist n * i + j - twist n ^ 2 * j := by ring
    _ = twist n * i := by rw [twist_sq hn]; ring

theorem conjugate_reflection_by_rotation (n : ℕ) (hn : 3 ≤ n)
    (i j : ZMod (modulus n)) :
    element n hn j 0 * element n hn i 1 * (element n hn j 0)⁻¹ =
      element n hn (i + (1 - twist n) * j) 1 := by
  rw [element_rotation_inv, element_rotation_mul, element_reflection_mul, add_zero]
  congr 1
  ring

theorem conjugate_reflection_by_reflection (n : ℕ) (hn : 3 ≤ n)
    (i j : ZMod (modulus n)) :
    element n hn j 1 * element n hn i 1 * (element n hn j 1)⁻¹ =
      element n hn (twist n * i + (1 - twist n) * j) 1 := by
  rw [element_reflection_inv, element_reflection_mul,
    show (1 + 1 : ZMod 2) = 0 by decide, element_rotation_mul]
  congr 1
  ring

theorem rotation_conjugacy_iff (n : ℕ) (hn : 3 ≤ n)
    (i : ZMod (modulus n)) (g : SemidihedralGroup n) :
    IsConj (element n hn i 0) g ↔
      g = element n hn i 0 ∨ g = element n hn (twist n * i) 0 := by
  rw [isConj_iff]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨⟨j, e⟩, rfl⟩ := (coordinateEquiv n hn).symm.surjective c
    change element n hn j e * element n hn i 0 * (element n hn j e)⁻¹ = g at hc
    rcases exponent_cases e with rfl | rfl
    · left
      rw [conjugate_rotation_by_rotation] at hc
      exact hc.symm
    · right
      rw [conjugate_rotation_by_reflection] at hc
      exact hc.symm
  · rintro (rfl | rfl)
    · exact ⟨1, by simp⟩
    · exact ⟨element n hn 0 1, conjugate_rotation_by_reflection n hn i 0⟩

theorem even_difference_conjugate (n : ℕ) (hn : 4 ≤ n)
    (i j k : ZMod (modulus n)) (hk : j - i = 2 * k) :
    IsConj (element n (by omega) i 1) (element n (by omega) j 1) := by
  obtain ⟨u, hu⟩ := quarter_sub_one_isUnit n hn
  have hmul : (1 - twist n) * (-(↑u⁻¹ * k)) = 2 * k := by
    calc
      (1 - twist n) * (-(↑u⁻¹ * k)) = (twist n - 1) * (↑u⁻¹ * k) := by ring
      _ = 2 * (↑u * (↑u⁻¹ * k)) := by
        rw [twist_sub_one_eq_two_mul n hn, ← hu]
        ring
      _ = 2 * k := by
        have huinv : (u : ZMod (modulus n)) * ↑u⁻¹ = 1 := Units.mul_inv u
        calc
          2 * (↑u * (↑u⁻¹ * k)) = 2 * ((↑u * ↑u⁻¹) * k) := by ring
          _ = 2 * k := by rw [huinv, one_mul]
  rw [isConj_iff]
  refine ⟨element n (by omega) (-(↑u⁻¹ * k)) 0, ?_⟩
  rw [conjugate_reflection_by_rotation, hmul]
  apply (element_eq_iff n (by omega) _ _ _ _).mpr
  refine ⟨?_, rfl⟩
  linear_combination -hk

theorem even_outside_conjugate (n : ℕ) (hn : 4 ≤ n) (j : ℤ) :
    IsConj (s n) (r n ^ (2 * j) * s n) := by
  rw [s_eq_element n (by omega), r_zpow_eq_element n (by omega),
    element_rotation_mul, add_zero]
  apply even_difference_conjugate n hn 0 _ (j : ZMod (modulus n))
  push_cast
  ring

theorem odd_outside_conjugate (n : ℕ) (hn : 4 ≤ n) (j : ℤ) :
    IsConj (r n * s n) (r n ^ (2 * j + 1) * s n) := by
  have hr : r n = element n (by omega) 1 0 := by
    simpa only [pow_one, Nat.cast_one] using r_pow_eq_element n (by omega) 1
  rw [r_zpow_eq_element n (by omega), hr, s_eq_element n (by omega),
    element_rotation_mul, element_rotation_mul, add_zero, add_zero]
  apply even_difference_conjugate n hn 1 _ (j : ZMod (modulus n))
  push_cast
  ring

end CFSG.Semidihedral
