module

public import CFSG.ClassicalInvolution.Q3.Q3ZAHeisDatum

public section

namespace CFSG.ClassicalInvolution.Q3.Q3ZA

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped MatrixGroups commutatorElement
open Matrix

@[expose] noncomputable def qSp : StatedSp 2 F3 := weyl₁ * sbU * weyl₁⁻¹

theorem uSL_eq : uSL = usl 1 := rfl

theorem lSL_eq : lSL = lsl 1 := rfl

theorem lb_usl_inv (k : Fin 2) (c : F3) :
    (longBlock F3 2 k (usl c))⁻¹ = longBlock F3 2 k (usl (-c)) := by
  rw [← map_inv, usl_inv]

theorem lb_usl_inl (k : Fin 2) (c : F3) :
    mat 2 F3 (longBlock F3 2 k (usl c)) *ᵥ Pi.single (Sum.inl k) 1 =
      (Pi.single (Sum.inl k) 1 : V4) := by
  rw [lb_mulVec_inl]
  simp [usl]

theorem lb_usl_inr (k : Fin 2) (c : F3) :
    mat 2 F3 (longBlock F3 2 k (usl c)) *ᵥ Pi.single (Sum.inr k) 1 =
      c • (Pi.single (Sum.inl k) 1 : V4) + Pi.single (Sum.inr k) 1 := by
  rw [lb_mulVec_inr]
  simp [usl]

theorem lb_lsl_inl (k : Fin 2) (c : F3) :
    mat 2 F3 (longBlock F3 2 k (lsl c)) *ᵥ Pi.single (Sum.inl k) 1 =
      (Pi.single (Sum.inl k) 1 : V4) + c • Pi.single (Sum.inr k) 1 := by
  rw [lb_mulVec_inl]
  simp [lsl]

theorem lb_lsl_inr (k : Fin 2) (c : F3) :
    mat 2 F3 (longBlock F3 2 k (lsl c)) *ᵥ Pi.single (Sum.inr k) 1 =
      (Pi.single (Sum.inr k) 1 : V4) := by
  rw [lb_mulVec_inr]
  simp [lsl]

theorem lb0u_e0 (c : F3) : mat 2 F3 (longBlock F3 2 0 (usl c)) *ᵥ bE0 = bE0 := lb_usl_inl 0 c
theorem lb0u_f0 (c : F3) :
    mat 2 F3 (longBlock F3 2 0 (usl c)) *ᵥ bF0 = c • bE0 + bF0 := lb_usl_inr 0 c
theorem lb0u_e1 (c : F3) : mat 2 F3 (longBlock F3 2 0 (usl c)) *ᵥ bE1 = bE1 :=
  lb_mulVec_other 0 _ (by simp [coords])
theorem lb0u_f1 (c : F3) : mat 2 F3 (longBlock F3 2 0 (usl c)) *ᵥ bF1 = bF1 :=
  lb_mulVec_other 0 _ (by simp [coords])
theorem lb1u_e1 (c : F3) : mat 2 F3 (longBlock F3 2 1 (usl c)) *ᵥ bE1 = bE1 := lb_usl_inl 1 c
theorem lb1u_f1 (c : F3) :
    mat 2 F3 (longBlock F3 2 1 (usl c)) *ᵥ bF1 = c • bE1 + bF1 := lb_usl_inr 1 c
theorem lb1u_e0 (c : F3) : mat 2 F3 (longBlock F3 2 1 (usl c)) *ᵥ bE0 = bE0 :=
  lb_mulVec_other 1 _ (by simp [coords])
theorem lb1u_f0 (c : F3) : mat 2 F3 (longBlock F3 2 1 (usl c)) *ᵥ bF0 = bF0 :=
  lb_mulVec_other 1 _ (by simp [coords])
theorem lb1l_e1 (c : F3) :
    mat 2 F3 (longBlock F3 2 1 (lsl c)) *ᵥ bE1 = bE1 + c • bF1 := lb_lsl_inl 1 c
theorem lb1l_f1 (c : F3) : mat 2 F3 (longBlock F3 2 1 (lsl c)) *ᵥ bF1 = bF1 := lb_lsl_inr 1 c
theorem lb1l_e0 (c : F3) : mat 2 F3 (longBlock F3 2 1 (lsl c)) *ᵥ bE0 = bE0 :=
  lb_mulVec_other 1 _ (by simp [coords])
theorem lb1l_f0 (c : F3) : mat 2 F3 (longBlock F3 2 1 (lsl c)) *ᵥ bF0 = bF0 :=
  lb_mulVec_other 1 _ (by simp [coords])

local macro "cross_simp" : tactic =>
  `(tactic| simp only [map_mul, ← Matrix.mulVec_mulVec, uSL_eq, lSL_eq, sbU_eq, sbL_eq, qSp,
    sb_usl_inv, sb_lsl_inv, lb_usl_inv, sb_usl_e0, sb_usl_e1, sb_usl_f0, sb_usl_f1, sb_lsl_e0,
    sb_lsl_e1, sb_lsl_f0, sb_lsl_f1, w1_e0, w1_e1, w1_f0, w1_f1, w0_e0, w0_e1, w0_f0, w0_f1,
    w1i_e0, w1i_e1, w1i_f0, w1i_f1, w0i_e0, w0i_e1, w0i_f0, w0i_f1, lb0u_e0, lb0u_f0, lb0u_e1,
    lb0u_f1, lb1u_e0, lb1u_f0, lb1u_e1, lb1u_f1, lb1l_e0, lb1l_f0, lb1l_e1, lb1l_f1,
    Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_smul, Matrix.mulVec_sub, map_one,
    Matrix.one_mulVec])

local macro "cross_close" : tactic =>
  `(tactic| first
    | module
    | (match_scalars <;>
        first
        | ring1
        | linear_combination three_eq_zero_f3
        | linear_combination (-1 : F3) * three_eq_zero_f3
        | linear_combination (2 : F3) * three_eq_zero_f3
        | linear_combination (-2 : F3) * three_eq_zero_f3))

theorem qSp_e0 : mat 2 F3 qSp *ᵥ bE0 = bE0 := by
  cross_simp

theorem qSp_e1 : mat 2 F3 qSp *ᵥ bE1 = bE1 := by
  cross_simp
  module

theorem qSp_f0 : mat 2 F3 qSp *ᵥ bF0 = bF0 + bE1 := by
  cross_simp
  module

theorem qSp_f1 : mat 2 F3 qSp *ᵥ bF1 = bF1 + bE0 := by
  cross_simp
  module

theorem M1 : longBlock F3 2 1 uSL * qSp = qSp * longBlock F3 2 1 uSL := by
  refine eq_of_mulVec_basis ?_ ?_ ?_ ?_ <;> (cross_simp; try module)

theorem M2 : longBlock F3 2 0 uSL * qSp = qSp * longBlock F3 2 0 uSL := by
  refine eq_of_mulVec_basis ?_ ?_ ?_ ?_ <;> (cross_simp; try module)

theorem M3 : longBlock F3 2 1 uSL * sbL = sbL * longBlock F3 2 1 uSL := by
  refine eq_of_mulVec_basis ?_ ?_ ?_ ?_ <;> (cross_simp; try module)

theorem M4 : longBlock F3 2 0 uSL * sbU = sbU * longBlock F3 2 0 uSL := by
  refine eq_of_mulVec_basis ?_ ?_ ?_ ?_ <;> (cross_simp; try module)

theorem M6' : qSp * sbL⁻¹ = (longBlock F3 2 1 uSL)⁻¹ * sbL⁻¹ * qSp := by
  refine eq_of_mulVec_basis ?_ ?_ ?_ ?_ <;> (cross_simp; try cross_close)

theorem M7' : qSp * sbU⁻¹ = (longBlock F3 2 0 uSL)⁻¹ * sbU⁻¹ * qSp := by
  refine eq_of_mulVec_basis ?_ ?_ ?_ ?_ <;> (cross_simp; try cross_close)

theorem M8' : longBlock F3 2 1 uSL * sbU⁻¹ =
    (longBlock F3 2 0 uSL)⁻¹ * qSp * sbU⁻¹ * longBlock F3 2 1 uSL := by
  refine eq_of_mulVec_basis ?_ ?_ ?_ ?_ <;> (cross_simp; try module)

theorem M9' : longBlock F3 2 1 lSL * qSp =
    (longBlock F3 2 0 uSL)⁻¹ * qSp * sbU⁻¹ * longBlock F3 2 1 lSL := by
  refine eq_of_mulVec_basis ?_ ?_ ?_ ?_ <;> (cross_simp; try module)

theorem M10 : longBlock F3 2 1 lSL * sbU = sbU * longBlock F3 2 1 lSL := by
  refine eq_of_mulVec_basis ?_ ?_ ?_ ?_ <;> (cross_simp; try module)

theorem usl_one_pow_three : usl 1 ^ 3 = 1 := by
  calc usl 1 ^ 3 = usl 1 * (usl 1 * usl 1) := pow_three _
    _ = usl (1 + (1 + 1)) := by rw [usl_add, usl_add]
    _ = usl 0 := by
      congr 1
      linear_combination three_eq_zero_f3
    _ = 1 := usl_zero

theorem lsl_one_pow_three : lsl 1 ^ 3 = 1 := by
  calc lsl 1 ^ 3 = lsl 1 * (lsl 1 * lsl 1) := pow_three _
    _ = lsl (1 + (1 + 1)) := by rw [lsl_add, lsl_add]
    _ = lsl 0 := by
      congr 1
      linear_combination three_eq_zero_f3
    _ = 1 := lsl_zero

theorem sbU_pow_three : sbU ^ 3 = 1 := by
  rw [sbU_eq, ← map_pow, usl_one_pow_three, map_one]

theorem sbL_pow_three : sbL ^ 3 = 1 := by
  rw [sbL_eq, ← map_pow, lsl_one_pow_three, map_one]

theorem lb_uSL_pow_three (k : Fin 2) : (longBlock F3 2 k uSL) ^ 3 = 1 := by
  rw [uSL_eq, ← map_pow, usl_one_pow_three, map_one]

theorem qSp_pow_three : qSp ^ 3 = 1 := by
  rw [qSp, conj_pow, sbU_pow_three, mul_one, mul_inv_cancel]

end CFSG.ClassicalInvolution.Q3.Q3ZA
