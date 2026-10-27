module

public import Mathlib.GroupTheory.OrderOfElement
import CFSG.GroupTheory.InvolutionPow
import Mathlib.Tactic.Group

public section

namespace CFSG.GroupTheory

theorem eq_one_of_odd_of_conj_eq_inv_of_commute {G : Type*} [Group G] {t u : G}
    (hu : Odd (orderOf u)) (hinv : t * u * t⁻¹ = u⁻¹) (hcomm : t * u = u * t) : u = 1 := by
  have hu2 : u * u = 1 := by
    have h1 : u = u⁻¹ := by
      rw [← hinv, hcomm]
      group
    simpa [← h1] using mul_inv_cancel u
  exact (CFSG.GroupTheory.pow_eq_self_of_odd_of_mul_self_eq_one hu2 hu).symm.trans
    (pow_orderOf_eq_one u)

theorem conj_pow_eq_mul {X : Type*} [Group X] {u x : X} (hux : u * x * u⁻¹ = x⁻¹)
    {k j : ℕ} (hk : k = 2 * j + 1) (hx : x ^ k = 1) :
    x ^ j * u * (x ^ j)⁻¹ = u * x := by
  have hconj : ∀ i : ℤ, u * x ^ i * u⁻¹ = (x ^ i)⁻¹ := by
    intro i
    rw [← conj_zpow, hux, inv_zpow]
  have hshift : x ^ (j : ℤ) * u = u * x ^ (-(j : ℤ)) := by
    calc x ^ (j : ℤ) * u = (u * x ^ (-(j : ℤ)) * u⁻¹) * u := by
          rw [hconj (-(j : ℤ))]
          simp
      _ = u * x ^ (-(j : ℤ)) := by group
  have hexp : x ^ (-(2 * (j : ℤ))) = x := by
    have hxk : x ^ (k : ℤ) = 1 := by simpa using hx
    rw [show -(2 * (j : ℤ)) = 1 - (k : ℤ) by
      rw [hk]
      push_cast
      ring, zpow_sub, hxk]
    simp
  calc x ^ j * u * (x ^ j)⁻¹ = x ^ (j : ℤ) * u * (x ^ (j : ℤ))⁻¹ := by simp
    _ = (u * x ^ (-(j : ℤ))) * (x ^ (-(j : ℤ))) := by rw [hshift, zpow_neg]
    _ = u * (x ^ (-(j : ℤ)) * x ^ (-(j : ℤ))) := by group
    _ = u * x ^ (-(j : ℤ) + -(j : ℤ)) := by rw [← zpow_add]
    _ = u * x ^ (-(2 * (j : ℤ))) := by rw [show -(j : ℤ) + -(j : ℤ) = -(2 * (j : ℤ)) by ring]
    _ = u * x := by rw [hexp]

end CFSG.GroupTheory
