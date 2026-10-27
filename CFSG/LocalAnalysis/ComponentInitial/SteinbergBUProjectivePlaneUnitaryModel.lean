module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneUnitaryFrame
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherHermitian

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

open Matrix CFSG.ClassicalGroups.UnitaryFlag UnitaryHigher

variable {r f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData r f K)

section Conj

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem isometry_conj_of_unitary {Q : GL ι K} {G : Matrix ι ι K}
    (hQ : ((Q : Matrix ι ι K).map h.bar)ᵀ * G * Q = 1) {Y : GL ι K}
    (hY : ((Y : Matrix ι ι K).map h.bar)ᵀ * Y = 1) :
    (((Q * Y * Q⁻¹ : GL ι K) : Matrix ι ι K).map h.bar)ᵀ * G *
      ((Q * Y * Q⁻¹ : GL ι K) : Matrix ι ι K) = G := by
  set Qm := (Q : Matrix ι ι K)
  set Qi := ((Q⁻¹ : GL ι K) : Matrix ι ι K)
  have hQQ : Qm * Qi = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hG : G = (Qi.map h.bar)ᵀ * Qi := by
    have h1 := conjTranspose_mul_mul h G Qm Qi
    rw [hQ, hQQ, conjT_one] at h1
    simpa only [Matrix.one_mul, Matrix.mul_one] using h1
  rw [Units.val_mul, Units.val_mul, conjTranspose_mul_mul, conjTranspose_mul_mul, hQ,
    Matrix.mul_one, hY, Matrix.mul_one, ← hG]

end Conj

end CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
