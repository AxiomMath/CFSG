module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearDescentFixedBasis

public section

namespace CFSG

noncomputable section

namespace GorensteinWalter

universe u

@[expose] def semilinearMatrixApply {n : ℕ} {K : Type u} [Field K]
    (A : GL (Fin n) K) (sigma : K ≃+* K) (v : Fin n → K) : Fin n → K :=
  Matrix.mulVec (A : Matrix (Fin n) (Fin n) K) (fun i => sigma (v i))

theorem semilinearMatrixApply_add {n : ℕ} {K : Type u} [Field K]
    (A : GL (Fin n) K) (sigma : K ≃+* K) (v w : Fin n → K) :
    semilinearMatrixApply A sigma (v + w) =
      semilinearMatrixApply A sigma v + semilinearMatrixApply A sigma w := by
  change Matrix.mulVec (A : Matrix (Fin n) (Fin n) K) (fun i => sigma (v i + w i)) = _
  simp_rw [map_add]
  exact Matrix.mulVec_add _ _ _

theorem semilinearMatrixApply_smul {n : ℕ} {K : Type u} [Field K]
    (A : GL (Fin n) K) (sigma : K ≃+* K) (a : K) (v : Fin n → K) :
    semilinearMatrixApply A sigma (a • v) =
      sigma a • semilinearMatrixApply A sigma v := by
  change Matrix.mulVec (A : Matrix (Fin n) (Fin n) K) (fun i => sigma (a * v i)) = _
  simp_rw [map_mul]
  exact Matrix.mulVec_smul _ (sigma a) _

theorem semilinearMatrixApply_involutive {n : ℕ} {K : Type u} [Field K]
    (A : GL (Fin n) K) (sigma : K ≃+* K)
    (hsigma : sigma ^ 2 = 1)
    (hA : A * Matrix.GeneralLinearGroup.map sigma.toRingHom A = 1) :
    Function.Involutive (semilinearMatrixApply A sigma) := by
  have hinvolution (x : K) : sigma (sigma x) = x := by
    simpa [pow_two] using DFunLike.congr_fun hsigma x
  have hmatrix : (A : Matrix (Fin n) (Fin n) K) *
      sigma.toRingHom.mapMatrix (A : Matrix (Fin n) (Fin n) K) = 1 :=
    congrArg Units.val hA
  intro v
  have hmap : (fun j => sigma (Matrix.mulVec (A : Matrix (Fin n) (Fin n) K)
      (fun k => sigma (v k)) j)) =
      (sigma.toRingHom.mapMatrix (A : Matrix (Fin n) (Fin n) K)).mulVec v := by
    funext j
    simpa [Function.comp_def, hinvolution] using
      sigma.toRingHom.map_mulVec (A : Matrix (Fin n) (Fin n) K) (fun k => sigma (v k)) j
  change Matrix.mulVec (A : Matrix (Fin n) (Fin n) K)
    (fun j => sigma (Matrix.mulVec (A : Matrix (Fin n) (Fin n) K) (fun k => sigma (v k)) j)) = v
  rw [hmap, Matrix.mulVec_mulVec, hmatrix, Matrix.one_mulVec]

theorem exists_semilinear_fixed_basis {n : ℕ} {K : Type u} [Field K]
    (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hsigma_ne : sigma ≠ 1)
    (htwo : (2 : K) ≠ 0)
    (T : (Fin n → K) ≃+ (Fin n → K))
    (hTinvol : Function.Involutive T)
    (hTsmul : ∀ (a : K) (v : Fin n → K), T (a • v) = sigma a • T v) :
    ∃ b : Module.Basis (Fin n) K (Fin n → K), ∀ j, T (b j) = b j :=
  ComponentClassification.CatalogueBLinearDescent.exists_fixed_coordinate_basis n sigma hsigma
    hsigma_ne htwo T hTinvol hTsmul

theorem exists_gl_semilinear_coboundary {n : ℕ} {K : Type u} [Field K]
    (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hsigma_ne : sigma ≠ 1)
    (htwo : (2 : K) ≠ 0)
    (A : GL (Fin n) K)
    (hA : A * Matrix.GeneralLinearGroup.map sigma.toRingHom A = 1) :
    ∃ C : GL (Fin n) K,
      A * Matrix.GeneralLinearGroup.map sigma.toRingHom C = C := by
  classical
  have hTinvol := semilinearMatrixApply_involutive A sigma hsigma hA
  let T : (Fin n → K) ≃+ (Fin n → K) := {
    toFun := semilinearMatrixApply A sigma
    invFun := semilinearMatrixApply A sigma
    left_inv := hTinvol
    right_inv := hTinvol
    map_add' := semilinearMatrixApply_add A sigma }
  obtain ⟨b, hb⟩ := exists_semilinear_fixed_basis sigma hsigma hsigma_ne htwo T hTinvol
    (semilinearMatrixApply_smul A sigma)
  let L : LinearMap.GeneralLinearGroup K (Fin n → K) :=
    LinearMap.GeneralLinearGroup.ofLinearEquiv b.equivFun.symm
  let C : GL (Fin n) K := Matrix.GeneralLinearGroup.toLin.symm L
  have hCcol (i j : Fin n) : (C : Matrix (Fin n) (Fin n) K) i j = b j i := by
    have hfun : Matrix.mulVec (C : Matrix (Fin n) (Fin n) K) (Pi.single j 1) = b j := by
      calc
        Matrix.mulVec (C : Matrix (Fin n) (Fin n) K) (Pi.single j 1) =
            (Matrix.GeneralLinearGroup.toLin C : (Fin n → K) → Fin n → K) (Pi.single j 1) := rfl
        _ = (L : (Fin n → K) → Fin n → K) (Pi.single j 1) := by
          rw [(Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := K)).apply_symm_apply]
        _ = b j := by simp [L, LinearMap.GeneralLinearGroup.ofLinearEquiv]
    rw [Matrix.mulVec_single_one] at hfun
    exact congrFun hfun i
  refine ⟨C, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  have hfix := congrFun (hb j) i
  change Matrix.mulVec (A : Matrix (Fin n) (Fin n) K) (fun k => sigma (b j k)) i = b j i at hfix
  simpa [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    hCcol] using hfix

end GorensteinWalter

end

end CFSG
