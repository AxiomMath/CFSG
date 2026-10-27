module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldAction
import CFSG.Dihedral.GorensteinWalter.GLSemilinearDescent

public section

namespace CFSG.ComponentClassification.CatalogueBLinearDescent

noncomputable section

open Matrix CatalogueBHigherLinearField

universe u

@[expose] def semilinearMatrixApply (n : ℕ) {K : Type u} [Field K]
    (A : GL (Fin n) K) (sigma : K ≃+* K) (v : Fin n → K) : Fin n → K :=
  A.val.mulVec (fun i => sigma (v i))

theorem semilinearMatrixApply_add (n : ℕ) {K : Type u} [Field K]
    (A : GL (Fin n) K) (sigma : K ≃+* K) (v w : Fin n → K) :
    semilinearMatrixApply n A sigma (v + w) =
      semilinearMatrixApply n A sigma v + semilinearMatrixApply n A sigma w :=
  GorensteinWalter.semilinearMatrixApply_add A sigma v w

theorem semilinearMatrixApply_smul (n : ℕ) {K : Type u} [Field K]
    (A : GL (Fin n) K) (sigma : K ≃+* K) (a : K) (v : Fin n → K) :
    semilinearMatrixApply n A sigma (a • v) =
      sigma a • semilinearMatrixApply n A sigma v :=
  GorensteinWalter.semilinearMatrixApply_smul A sigma a v

theorem semilinearMatrixApply_involutive (n : ℕ) {K : Type u} [Field K]
    (A : GL (Fin n) K) (sigma : K ≃+* K)
    (hsigma : sigma ^ 2 = 1) (hA : A * glFieldAut (Fin n) K sigma A = 1) :
    Function.Involutive (semilinearMatrixApply n A sigma) :=
  GorensteinWalter.semilinearMatrixApply_involutive A sigma hsigma hA

theorem exists_gl_semilinear_coboundary (n : ℕ) {K : Type u} [Field K]
    (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (htwo : (2 : K) ≠ 0) (A : GL (Fin n) K)
    (hA : A * glFieldAut (Fin n) K sigma A = 1) :
    ∃ H : GL (Fin n) K, A * glFieldAut (Fin n) K sigma H = H :=
  GorensteinWalter.exists_gl_semilinear_coboundary sigma hsigma hne htwo A hA

end

end CFSG.ComponentClassification.CatalogueBLinearDescent
