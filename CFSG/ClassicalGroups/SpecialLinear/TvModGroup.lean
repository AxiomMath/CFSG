module

public import CFSG.LargeExtraspecial.A2ModSLc

public section

namespace CFSG.ClassicalGroups.SpecialLinear.TvMod

open Matrix CFSG.LargeExtraspecial.A2Mod

variable {n : ℕ}

section CommRing

variable {R : Type*} [CommRing R]

private theorem transpose_inv_mul_transpose (g : SpecialLinearGroup (Fin n) R) :
    SpecialLinearGroup.transpose g⁻¹ * SpecialLinearGroup.transpose g = 1 := by
  refine Subtype.ext ?_
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_transpose,
    SpecialLinearGroup.coe_transpose, ← transpose_mul, sl_coe_mul_coe_inv, transpose_one,
    SpecialLinearGroup.coe_one]

private theorem inv_transpose_inv (g : SpecialLinearGroup (Fin n) R) :
    (SpecialLinearGroup.transpose g⁻¹)⁻¹ = SpecialLinearGroup.transpose g :=
  inv_eq_of_mul_eq_one_right (transpose_inv_mul_transpose g)

private theorem transpose_transpose_sl (g : SpecialLinearGroup (Fin n) R) :
    SpecialLinearGroup.transpose (SpecialLinearGroup.transpose g) = g :=
  Subtype.ext (by rw [SpecialLinearGroup.coe_transpose, SpecialLinearGroup.coe_transpose,
    transpose_transpose])

noncomputable def invTranspose : SpecialLinearGroup (Fin n) R ≃* SpecialLinearGroup (Fin n) R where
  toFun g := SpecialLinearGroup.transpose g⁻¹
  invFun g := SpecialLinearGroup.transpose g⁻¹
  left_inv g := by
    show SpecialLinearGroup.transpose (SpecialLinearGroup.transpose g⁻¹)⁻¹ = g
    rw [inv_transpose_inv, transpose_transpose_sl]
  right_inv g := by
    show SpecialLinearGroup.transpose (SpecialLinearGroup.transpose g⁻¹)⁻¹ = g
    rw [inv_transpose_inv, transpose_transpose_sl]
  map_mul' g h := Subtype.ext (by
    show ((SpecialLinearGroup.transpose (g * h)⁻¹ : SpecialLinearGroup (Fin n) R) :
      Matrix (Fin n) (Fin n) R) = ((SpecialLinearGroup.transpose g⁻¹ *
        SpecialLinearGroup.transpose h⁻¹ : SpecialLinearGroup (Fin n) R) :
      Matrix (Fin n) (Fin n) R)
    rw [_root_.mul_inv_rev, SpecialLinearGroup.coe_transpose, SpecialLinearGroup.coe_mul,
      SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_transpose,
      SpecialLinearGroup.coe_transpose, transpose_mul])

theorem coe_invTranspose (g : SpecialLinearGroup (Fin n) R) :
    ((invTranspose g : SpecialLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) =
      ((g⁻¹ : SpecialLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R)ᵀ := by
  unfold invTranspose
  rfl

theorem invTranspose_invTranspose (g : SpecialLinearGroup (Fin n) R) :
    invTranspose (invTranspose g) = g := by
  refine Subtype.ext ?_
  rw [coe_invTranspose, ← map_inv invTranspose g, coe_invTranspose, inv_inv, transpose_transpose]

end CommRing

section Two

theorem invTranspose_tv (v φ : Fin n → ZMod 2) : invTranspose (tv v φ) = tv φ v := by
  by_cases h : φ ⬝ᵥ v = 0
  · have h' : v ⬝ᵥ φ = 0 := by rw [dotProduct_comm, h]
    refine Subtype.ext ?_
    rw [coe_invTranspose, tv_inv_eq_self, coe_tv h, coe_tv h', transpose_add, transpose_one,
      transpose_vecMulVec]
  · have h' : v ⬝ᵥ φ ≠ 0 := by rwa [dotProduct_comm]
    rw [tv_of_dotProduct_ne_zero h, tv_of_dotProduct_ne_zero h', map_one]

end Two

end CFSG.ClassicalGroups.SpecialLinear.TvMod
