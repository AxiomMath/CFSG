module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutAut74Coord

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23

private lemma two_add_F4c' : ∀ x : F4c, x + x = 0 := by decide +kernel

private lemma pow_four_F4c' : ∀ x : F4c, x * x * (x * x) = x := by decide +kernel

private lemma add_sq_F4c' : ∀ x y : F4c, (x + y) * (x + y) = x * x + y * y := by
  decide +kernel

@[expose] def torusAut (u v : F4c) (hu : u ≠ 0) (hv : v ≠ 0) : MulAut U4 where
  toFun x := ⟨u * x.a, v * x.b, u * v * x.c⟩
  invFun x := ⟨u⁻¹ * x.a, v⁻¹ * x.b, u⁻¹ * v⁻¹ * x.c⟩
  left_inv := fun x => by
    refine UT3.ext ?_ ?_ ?_
    · show u⁻¹ * (u * x.a) = x.a
      rw [← mul_assoc, inv_mul_cancel₀ hu, one_mul]
    · show v⁻¹ * (v * x.b) = x.b
      rw [← mul_assoc, inv_mul_cancel₀ hv, one_mul]
    · calc u⁻¹ * v⁻¹ * (u * v * x.c)
          = (u⁻¹ * u) * (v⁻¹ * v) * x.c := by ring
        _ = 1 * 1 * x.c := by rw [inv_mul_cancel₀ hu, inv_mul_cancel₀ hv]
        _ = x.c := by ring
  right_inv := fun x => by
    refine UT3.ext ?_ ?_ ?_
    · show u * (u⁻¹ * x.a) = x.a
      rw [← mul_assoc, mul_inv_cancel₀ hu, one_mul]
    · show v * (v⁻¹ * x.b) = x.b
      rw [← mul_assoc, mul_inv_cancel₀ hv, one_mul]
    · calc u * v * (u⁻¹ * v⁻¹ * x.c)
          = (u * u⁻¹) * (v * v⁻¹) * x.c := by ring
        _ = 1 * 1 * x.c := by rw [mul_inv_cancel₀ hu, mul_inv_cancel₀ hv]
        _ = x.c := by ring
  map_mul' := fun x y => by
    refine UT3.ext ?_ ?_ ?_
    · simp only [UT3.mul_def]
      ring
    · simp only [UT3.mul_def]
      ring
    · simp only [UT3.mul_def]
      ring

@[expose] def frobAut : MulAut U4 where
  toFun x := ⟨x.a * x.a, x.b * x.b, x.c * x.c⟩
  invFun x := ⟨x.a * x.a, x.b * x.b, x.c * x.c⟩
  left_inv := fun x => by
    refine UT3.ext ?_ ?_ ?_
    · exact pow_four_F4c' x.a
    · exact pow_four_F4c' x.b
    · exact pow_four_F4c' x.c
  right_inv := fun x => by
    refine UT3.ext ?_ ?_ ?_
    · exact pow_four_F4c' x.a
    · exact pow_four_F4c' x.b
    · exact pow_four_F4c' x.c
  map_mul' := fun x y => by
    refine UT3.ext ?_ ?_ ?_
    · simp only [UT3.mul_def]
      exact add_sq_F4c' x.a y.a
    · simp only [UT3.mul_def]
      exact add_sq_F4c' x.b y.b
    · simp only [UT3.mul_def]
      calc (x.c + y.c + x.a * y.b) * (x.c + y.c + x.a * y.b)
          = (x.c + y.c) * (x.c + y.c) + (x.a * y.b) * (x.a * y.b) :=
            add_sq_F4c' (x.c + y.c) (x.a * y.b)
        _ = (x.c * x.c + y.c * y.c) + (x.a * x.a) * (y.b * y.b) := by
            rw [add_sq_F4c' x.c y.c]
            ring

@[expose] def swapAut : MulAut U4 where
  toFun x := ⟨x.b, x.a, x.c + x.a * x.b⟩
  invFun x := ⟨x.b, x.a, x.c + x.a * x.b⟩
  left_inv := fun x => by
    refine UT3.ext rfl rfl ?_
    have h : x.a * x.b + x.b * x.a = 0 := by
      rw [mul_comm x.b x.a]
      exact two_add_F4c' (x.a * x.b)
    linear_combination h
  right_inv := fun x => by
    refine UT3.ext rfl rfl ?_
    have h : x.a * x.b + x.b * x.a = 0 := by
      rw [mul_comm x.b x.a]
      exact two_add_F4c' (x.a * x.b)
    linear_combination h
  map_mul' := fun x y => by
    refine UT3.ext ?_ ?_ ?_
    · simp only [UT3.mul_def]
    · simp only [UT3.mul_def]
    · simp only [UT3.mul_def]
      have h : x.a * y.b + x.a * y.b = 0 := two_add_F4c' (x.a * y.b)
      linear_combination h

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
