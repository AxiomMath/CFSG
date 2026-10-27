module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84FLMat

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace FL

open Certificates.A5GL42 (Mat4 Vec4)
open Matrix

@[expose] def twice (v : Vec4) : Fin 4 → ZMod 4 := fun i => 2 * lift (v i)

theorem two_mul_eq_iff (x y : ZMod 4) : 2 * x = 2 * y ↔ red x = red y := by
  revert x y
  decide

theorem twice_injective : Function.Injective twice := by
  intro v w h
  funext i
  have h1 := congrFun h i
  simp only [twice] at h1
  have h2 := (two_mul_eq_iff _ _).1 h1
  simpa [red_lift] using h2

theorem twice_zero : twice 0 = 0 := by
  funext i
  simp only [twice, Pi.zero_apply]
  have : lift (0 : ZMod 2) = 0 := by decide
  rw [this, mul_zero]

theorem twice_ne_zero {v : Vec4} (hv : v ≠ 0) : twice v ≠ 0 := by
  intro h
  exact hv (twice_injective (h.trans twice_zero.symm))

theorem mulVec_twice (M : M4) (v : Vec4) : M *ᵥ twice v = twice (redM M *ᵥ v) := by
  funext i
  have h1 : (M *ᵥ twice v) i = 2 * ∑ j, M i j * lift (v j) := by
    simp only [Matrix.mulVec, dotProduct, twice, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : twice (redM M *ᵥ v) i = 2 * lift (∑ j, red (M i j) * v j) := by
    simp [twice, Matrix.mulVec, dotProduct, redM_apply]
  rw [h1, h2, two_mul_eq_iff, map_sum, red_lift]
  exact Finset.sum_congr rfl fun j _ => by rw [map_mul, red_lift]

end FL

end CFSG.OddStandard.SmallF3.Omega
