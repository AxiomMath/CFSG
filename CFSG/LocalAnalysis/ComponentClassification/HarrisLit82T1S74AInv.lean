module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.Universal.Spin.Chevalley.Basic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup CliffordAlgebra QuadraticMap CFSG.LieType.Universal.Spin
open scoped MatrixGroups

section Clifford

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)

theorem commute_ι_ι_mul_ι {a b c : V} (ha : polar Q c a = 0) (hb : polar Q c b = 0) :
    Commute (ι Q c) (ι Q a * ι Q b) := by
  show ι Q c * (ι Q a * ι Q b) = ι Q a * ι Q b * ι Q c
  rw [← mul_assoc, ι_mul_ι_eq_neg_of_polar_eq_zero Q ha, neg_mul, mul_assoc,
    ι_mul_ι_eq_neg_of_polar_eq_zero Q hb, mul_neg, neg_neg]
  simp only [mul_assoc]

theorem commute_ι_triple_left {a b d : V} (hab : polar Q a b = 0) (had : polar Q a d = 0) :
    Commute (ι Q a) (ι Q a * ι Q b * ι Q d) := by
  rw [mul_assoc]
  exact (Commute.refl _).mul_right (commute_ι_ι_mul_ι Q hab had)

theorem commute_ι_triple_mid {a b d : V} (hba : polar Q b a = 0) (hbd : polar Q b d = 0) :
    Commute (ι Q b) (ι Q a * ι Q b * ι Q d) := by
  have hab : polar Q a b = 0 := by rw [polar_comm]; exact hba
  rw [ι_mul_ι_eq_neg_of_polar_eq_zero Q hab, neg_mul, mul_assoc]
  exact ((Commute.refl _).mul_right (commute_ι_ι_mul_ι Q hba hbd)).neg_right

theorem commute_ι_triple_right {a b d : V} (hda : polar Q d a = 0) (hdb : polar Q d b = 0) :
    Commute (ι Q d) (ι Q a * ι Q b * ι Q d) :=
  (commute_ι_ι_mul_ι Q hda hdb).mul_right (Commute.refl _)

theorem ι_mul_ι_mul_self_of_polar {x y : V} (h : polar Q y x = 0) :
    ι Q x * ι Q y * (ι Q x * ι Q y) = -algebraMap K (CliffordAlgebra Q) (Q x * Q y) := by
  calc ι Q x * ι Q y * (ι Q x * ι Q y) = ι Q x * (ι Q y * ι Q x) * ι Q y := by
        simp only [mul_assoc]
    _ = ι Q x * (-(ι Q x * ι Q y)) * ι Q y := by rw [ι_mul_ι_eq_neg_of_polar_eq_zero Q h]
    _ = -((ι Q x * ι Q x) * (ι Q y * ι Q y)) := by noncomm_ring
    _ = -algebraMap K (CliffordAlgebra Q) (Q x * Q y) := by
        rw [ι_sq_scalar, ι_sq_scalar, map_mul]

end Clifford

section Pair

variable {K : Type*} [Field K]

theorem SL2Pair.mul_toFun_of_mul_eq {A : Type*} [Ring A] [Algebra K A] (P P' : SL2Pair A)
    {g : A} (hX : g * P.X = -P'.Y * g) (hY : g * P.Y = -P'.X * g)
    (M : Matrix (Fin 2) (Fin 2) K) :
    g * P.toFun M = P'.toFun !![M 1 1, -M 1 0; -M 0 1, M 0 0] * g := by
  have hXY : g * (P.X * P.Y) = P'.Y * P'.X * g := by
    calc g * (P.X * P.Y) = g * P.X * P.Y := (mul_assoc _ _ _).symm
      _ = -P'.Y * g * P.Y := by rw [hX]
      _ = -(P'.Y * (g * P.Y)) := by noncomm_ring
      _ = P'.Y * P'.X * g := by rw [hY]; noncomm_ring
  have hYX : g * (P.Y * P.X) = P'.X * P'.Y * g := by
    calc g * (P.Y * P.X) = g * P.Y * P.X := (mul_assoc _ _ _).symm
      _ = -P'.X * g * P.X := by rw [hY]
      _ = -(P'.X * (g * P.X)) := by noncomm_ring
      _ = P'.X * P'.Y * g := by rw [hX]; noncomm_ring
  simp only [SL2Pair.toFun, mul_add, mul_sub, add_mul, sub_mul, mul_smul_comm, smul_mul_assoc,
    mul_one, one_mul, hXY, hYX, hX, hY, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, neg_mul, smul_neg,
    neg_smul]
  module

@[expose] def slTwist (M : SL(2, K)) : SL(2, K) :=
  ⟨!![M 1 1, -M 1 0; -M 0 1, M 0 0], by
    have h := M.det_coe
    rw [Matrix.det_fin_two] at h
    rw [Matrix.det_fin_two_of]
    linear_combination h⟩

theorem coe_slTwist (M : SL(2, K)) :
    (slTwist M : Matrix (Fin 2) (Fin 2) K) = !![M 1 1, -M 1 0; -M 0 1, M 0 0] := rfl

theorem slTwist_slTwist (M : SL(2, K)) : slTwist (slTwist M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_slTwist]

theorem slTwist_neg_one : slTwist (-1 : SL(2, K)) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_slTwist]

end Pair

end CFSG.ComponentClassification.HarrisLit.T1.S74
