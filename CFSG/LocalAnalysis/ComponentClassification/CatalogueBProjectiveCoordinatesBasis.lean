module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveCoordinatesMatrix

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBProjectiveCoordinates

variable {ι K V : Type*} [Fintype ι] [DecidableEq ι] [Field K]
  [AddCommGroup V] [Module K V]

@[expose] def basisAutomorphismMatrixEquiv (b : Module.Basis ι K V) :
    (V ≃ₗ[K] V) ≃* Matrix.GeneralLinearGroup ι K :=
  ((Matrix.GeneralLinearGroup.toLin' b).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K V)).symm

theorem basisAutomorphismMatrixEquiv_symm_apply (b : Module.Basis ι K V)
    (A : Matrix.GeneralLinearGroup ι K) (v : V) :
    (basisAutomorphismMatrixEquiv b).symm A v =
      b.equivFun.symm (matrixActionEquiv A (b.equivFun v)) := rfl

theorem basisAutomorphismMatrixEquiv_action (b : Module.Basis ι K V)
    (B : V ≃ₗ[K] V) (v : V) :
    b.equivFun.symm
        (matrixActionEquiv (basisAutomorphismMatrixEquiv b B) (b.equivFun v)) = B v := by
  rw [← basisAutomorphismMatrixEquiv_symm_apply]
  exact congrArg (fun C : V ≃ₗ[K] V => C v)
    ((basisAutomorphismMatrixEquiv b).symm_apply_apply B)

theorem basisAutomorphismMatrixEquiv_mulVec (b : Module.Basis ι K V)
    (B : V ≃ₗ[K] V) (v : V) :
    (basisAutomorphismMatrixEquiv b B).val.mulVec (b.equivFun v) = b.equivFun (B v) := by
  have h := congrArg b.equivFun (basisAutomorphismMatrixEquiv_action b B v)
  simpa only [LinearEquiv.apply_symm_apply, matrixActionEquiv_apply] using h

theorem basisAutomorphismMatrixEquiv_scalar (b : Module.Basis ι K V) (c : Kˣ) :
    basisAutomorphismMatrixEquiv b (LinearEquiv.smulOfUnit c) =
      Matrix.GeneralLinearGroup.scalar ι c := by
  apply (basisAutomorphismMatrixEquiv b).symm.injective
  rw [MulEquiv.symm_apply_apply]
  ext v
  rw [basisAutomorphismMatrixEquiv_symm_apply, matrixActionEquiv_scalar]
  change c.val • v = b.equivFun.symm (c.val • b.equivFun v)
  rw [map_smul, LinearEquiv.symm_apply_apply]

theorem basisAutomorphismMatrixEquiv_symm_scalar (b : Module.Basis ι K V) (c : Kˣ) :
    (basisAutomorphismMatrixEquiv b).symm (Matrix.GeneralLinearGroup.scalar ι c) =
      LinearEquiv.smulOfUnit c := by
  rw [← basisAutomorphismMatrixEquiv_scalar b c, MulEquiv.symm_apply_apply]

variable (K V) [FiniteDimensional K V]

@[expose] def automorphismMatrixEquiv :
    (V ≃ₗ[K] V) ≃* Matrix.GeneralLinearGroup (Fin (Module.finrank K V)) K :=
  basisAutomorphismMatrixEquiv (Module.finBasis K V)

theorem automorphismMatrixEquiv_action (B : V ≃ₗ[K] V) (v : V) :
    (Module.finBasis K V).equivFun.symm
        (matrixActionEquiv (automorphismMatrixEquiv K V B)
          ((Module.finBasis K V).equivFun v)) = B v :=
  basisAutomorphismMatrixEquiv_action (Module.finBasis K V) B v

theorem automorphismMatrixEquiv_mulVec (B : V ≃ₗ[K] V) (v : V) :
    (automorphismMatrixEquiv K V B).val.mulVec ((Module.finBasis K V).equivFun v) =
      (Module.finBasis K V).equivFun (B v) :=
  basisAutomorphismMatrixEquiv_mulVec (Module.finBasis K V) B v

theorem automorphismMatrixEquiv_scalar (c : Kˣ) :
    automorphismMatrixEquiv K V (LinearEquiv.smulOfUnit c) =
      Matrix.GeneralLinearGroup.scalar (Fin (Module.finrank K V)) c :=
  basisAutomorphismMatrixEquiv_scalar (Module.finBasis K V) c

theorem automorphismMatrixEquiv_symm_scalar (c : Kˣ) :
    (automorphismMatrixEquiv K V).symm
        (Matrix.GeneralLinearGroup.scalar (Fin (Module.finrank K V)) c) =
      LinearEquiv.smulOfUnit c :=
  basisAutomorphismMatrixEquiv_symm_scalar (Module.finBasis K V) c

end CFSG.ComponentClassification.CatalogueBProjectiveCoordinates
