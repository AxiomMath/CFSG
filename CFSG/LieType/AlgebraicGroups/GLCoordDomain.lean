module

public import CFSG.LieType.AlgebraicGroups.GLCoordHopf
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open MvPolynomial

variable (k : Type*) [Field k] (ι : Type*) [Fintype ι] [DecidableEq ι]

@[expose] def matCoordDet : MvPolynomial (ι × ι) k := (Matrix.mvPolynomialX ι ι k).det

@[expose] def glCoordToLocalization : GLCoord k ι →ₐ[k] Localization.Away (matCoordDet k ι) :=
  GLCoord.lift k ι
    ((algebraMap (MvPolynomial (ι × ι) k) (Localization.Away (matCoordDet k ι))).mapMatrix
      (Matrix.mvPolynomialX ι ι k))
    (IsLocalization.Away.invSelf (matCoordDet k ι)) (by
      rw [← RingHom.map_det]
      exact IsLocalization.Away.mul_invSelf (matCoordDet k ι))

theorem glCoordToLocalization_glEntry (i j : ι) :
    glCoordToLocalization k ι (glEntry k ι i j) =
      algebraMap (MvPolynomial (ι × ι) k) (Localization.Away (matCoordDet k ι)) (X (i, j)) :=
  GLCoord.lift_glEntry k ι _ _ _ i j

theorem glCoordToLocalization_glDetInv :
    glCoordToLocalization k ι (glDetInv k ι) = IsLocalization.Away.invSelf (matCoordDet k ι) :=
  GLCoord.lift_glDetInv k ι _ _ _

theorem aeval_matCoordDet :
    aeval (fun p : ι × ι => glEntry k ι p.1 p.2) (matCoordDet k ι) = (glEntryMatrix k ι).det := by
  rw [matCoordDet, AlgHom.map_det]
  congr 1
  ext i j
  simp

theorem isUnit_aeval_matCoordDet :
    IsUnit (aeval (fun p : ι × ι => glEntry k ι p.1 p.2) (matCoordDet k ι)) := by
  rw [aeval_matCoordDet]
  exact IsUnit.of_mul_eq_one _ (det_glEntryMatrix_mul_glDetInv k ι)

@[expose] def localizationToGLCoord : Localization.Away (matCoordDet k ι) →ₐ[k] GLCoord k ι :=
  IsLocalization.Away.liftAlgHom (matCoordDet k ι) (isUnit_aeval_matCoordDet k ι)

theorem localizationToGLCoord_algebraMap (a : MvPolynomial (ι × ι) k) :
    localizationToGLCoord k ι (algebraMap _ _ a) = aeval (fun p : ι × ι => glEntry k ι p.1 p.2) a :=
  IsLocalization.Away.lift_eq (matCoordDet k ι) (isUnit_aeval_matCoordDet k ι) a

@[expose] def glCoordEquivLocalization : GLCoord k ι ≃ₐ[k] Localization.Away (matCoordDet k ι) :=
  AlgEquiv.ofAlgHom (glCoordToLocalization k ι) (localizationToGLCoord k ι)
    (IsLocalization.algHom_ext (Submonoid.powers (matCoordDet k ι))
      (MvPolynomial.algHom_ext fun p => by
        change glCoordToLocalization k ι (localizationToGLCoord k ι (algebraMap _ _ (X p))) =
          algebraMap _ _ (X p)
        rw [localizationToGLCoord_algebraMap, aeval_X, glCoordToLocalization_glEntry]))
    (GLCoord.algHom_ext k ι (fun i j => by
        simp only [AlgHom.comp_apply, glCoordToLocalization_glEntry,
          localizationToGLCoord_algebraMap, aeval_X, AlgHom.id_apply]) (by
        simp only [AlgHom.comp_apply, glCoordToLocalization_glDetInv, AlgHom.id_apply]
        have h : localizationToGLCoord k ι (algebraMap _ _ (matCoordDet k ι)) *
            localizationToGLCoord k ι (IsLocalization.Away.invSelf (matCoordDet k ι)) = 1 := by
          rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
        rw [localizationToGLCoord_algebraMap, aeval_matCoordDet] at h
        exact (IsUnit.of_mul_eq_one _ h).mul_left_cancel
          (h.trans (det_glEntryMatrix_mul_glDetInv k ι).symm)))

instance : IsDomain (GLCoord k ι) :=
  have : IsDomain (Localization.Away (matCoordDet k ι)) :=
    IsLocalization.Away.isDomain _ (x := matCoordDet k ι) (Matrix.det_mvPolynomialX_ne_zero ι k)
  MulEquiv.isDomain _ (glCoordEquivLocalization k ι).toRingEquiv.toMulEquiv

end CFSG.LieType.AlgebraicGroups
