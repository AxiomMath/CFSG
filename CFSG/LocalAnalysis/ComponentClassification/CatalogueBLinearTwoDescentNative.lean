module

import CFSG.Adapters.QiuzhenLegacy.GorensteinWalter.PGammaL2ProjectiveHilbert90
public import CFSG.Dihedral.GorensteinWalter.GLSemilinearDescent
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PureSemilinear
public import CFSG.Assembly.Defs

public section

namespace CFSG.ComponentClassification.CatalogueBLinearTwoDescent

noncomputable section

open CFSG.GorensteinWalter

universe u

@[expose] def matrixSemilinearApply {K : Type u} [Field K]
    (A : Matrix.GeneralLinearGroup (Fin 2) K) (sigma : K ≃+* K)
    (v : Fin 2 → K) : Fin 2 → K :=
  Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) K) (fun i => sigma (v i))

theorem matrixSemilinearApply_involutive {K : Type u} [Field K]
    (A : Matrix.GeneralLinearGroup (Fin 2) K) (sigma : K ≃+* K)
    (hsigma : sigma ^ 2 = 1)
    (hA : A * Matrix.GeneralLinearGroup.map sigma.toRingHom A = 1) :
    Function.Involutive (matrixSemilinearApply A sigma) :=
  CFSG.GorensteinWalter.semilinearMatrixApply_involutive A sigma hsigma hA

theorem matrixSemilinear_fixed_basis {K : Type u} [Field K]
    (A : Matrix.GeneralLinearGroup (Fin 2) K) (sigma : K ≃+* K)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (htwo : (2 : K) ≠ 0)
    (hA : A * Matrix.GeneralLinearGroup.map sigma.toRingHom A = 1) :
    ∃ b : Module.Basis (Fin 2) K (Fin 2 → K),
      ∀ j, matrixSemilinearApply A sigma (b j) = b j := by
  let T : (Fin 2 → K) ≃+ (Fin 2 → K) := {
    toFun := matrixSemilinearApply A sigma
    invFun := matrixSemilinearApply A sigma
    left_inv := matrixSemilinearApply_involutive A sigma hsigma hA
    right_inv := matrixSemilinearApply_involutive A sigma hsigma hA
    map_add' := CFSG.GorensteinWalter.semilinearMatrixApply_add A sigma }
  exact CFSG.GorensteinWalter.exists_semilinear_fixed_basis sigma hsigma hne htwo T
    (matrixSemilinearApply_involutive A sigma hsigma hA)
    (CFSG.GorensteinWalter.semilinearMatrixApply_smul A sigma)

theorem matrixSemilinear_coboundary {K : Type u} [Field K]
    (A : Matrix.GeneralLinearGroup (Fin 2) K) (sigma : K ≃+* K)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (htwo : (2 : K) ≠ 0)
    (hA : A * Matrix.GeneralLinearGroup.map sigma.toRingHom A = 1) :
    ∃ H : Matrix.GeneralLinearGroup (Fin 2) K,
      A * Matrix.GeneralLinearGroup.map sigma.toRingHom H = H :=
  CFSG.GorensteinWalter.exists_gl_semilinear_coboundary sigma hsigma hne htwo A hA

theorem projectiveCocycle_exactGL_lift {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (A : Matrix.GeneralLinearGroup (Fin 2) K) (sigma : K ≃+* K)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hA : Matrix.ProjGenLinGroup.mk A *
      pgl2RingEquiv sigma (Matrix.ProjGenLinGroup.mk A) = 1) :
    ∃ B : Matrix.GeneralLinearGroup (Fin 2) K,
      Matrix.ProjGenLinGroup.mk B = Matrix.ProjGenLinGroup.mk A ∧
        B * Matrix.GeneralLinearGroup.map sigma.toRingHom B = 1 :=
  CFSG.GorensteinWalter.exists_exact_gl_lift_of_projective_cocycle hK sigma hsigma hne A hA

theorem native_semilinear_involution_conjugacy
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (a : PGammaL2 K) (ha : orderOf a = 2) (hfield : a.right ≠ 1) :
    ∃ h : PGL2 K,
      a = SemidirectProduct.inl h * SemidirectProduct.inr a.right *
        (SemidirectProduct.inl h)⁻¹ := by
  obtain ⟨h, hh⟩ :=
    CFSG.GorensteinWalter.projective_semilinear_involution_conj_inr
      hK a ha hfield
  refine ⟨h, ?_⟩
  calc
    a = SemidirectProduct.inl h *
        ((SemidirectProduct.inl h)⁻¹ * a * SemidirectProduct.inl h) *
        (SemidirectProduct.inl h)⁻¹ := by group
    _ = _ := by rw [hh]


end

end CFSG.ComponentClassification.CatalogueBLinearTwoDescent
