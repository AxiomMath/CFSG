module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionProjective
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataQuotient

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointData

open Matrix CatalogueBOrthogonalSemilinear
open QuadraticMap CFSG.ClassicalGroups.Orthogonal

universe u

variable {K : Type u} [Field K] {d : ℕ}

theorem matrixLinearIso_apply_eq (A : GL (Fin d) K) :
    matrixLinearIso A = matrixLinearEquiv A := rfl

theorem matrixDerived_map_native (Q : QuadraticForm K (Fin d → K)) :
    (matrixDerived Q).map matrixLinearIso.toMonoidHom =
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  rw [matrixDerived, Subgroup.map_commutator, matrixIsometries]
  rw [Subgroup.map_comap_eq_self_of_surjective matrixLinearIso.surjective]

theorem matrixDerived_comap_native (Q : QuadraticForm K (Fin d → K)) :
    matrixDerived Q =
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆.comap
        matrixLinearIso.toMonoidHom := by
  rw [matrixDerived, matrixIsometries,
    Subgroup.comap_equiv_eq_map_symm' matrixLinearIso,
    ← Subgroup.map_commutator,
    Subgroup.comap_equiv_eq_map_symm' matrixLinearIso]

@[expose] def matrixNativeDerivedEquiv (Q : QuadraticForm K (Fin d → K)) :
    matrixDerived Q ≃*
      ↥(⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆) :=
  (matrixLinearIso.subgroupMap (matrixDerived Q)).trans
    (MulEquiv.subgroupCongr (matrixDerived_map_native Q))

theorem matrixNativeDerivedEquiv_val (Q : QuadraticForm K (Fin d → K))
    (A : matrixDerived Q) :
    (matrixNativeDerivedEquiv Q A).val = matrixLinearEquiv A.val := rfl

@[expose] def matrixNativeElementaryEquiv (Q : QuadraticForm K (Fin d → K))
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) : matrixDerived Q ≃* elementaryGroup Q :=
  (matrixNativeDerivedEquiv Q).trans (MulEquiv.subgroupCongr hE)

theorem matrixNativeElementaryEquiv_val (Q : QuadraticForm K (Fin d → K))
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (A : matrixDerived Q) :
    (matrixNativeElementaryEquiv Q hE A).val = matrixLinearEquiv A.val := rfl

theorem matrixNativeElementaryEquiv_scalars (Q : QuadraticForm K (Fin d → K))
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) :
    (matrixDerivedScalars Q).map (matrixNativeElementaryEquiv Q hE).toMonoidHom =
      CatalogueBOrthogonalPointAction.scalarKernel Q := by
  ext x
  constructor
  · rintro ⟨A, hA, rfl⟩
    obtain ⟨c, hc⟩ := (mem_matrixDerivedScalars_iff Q A).mp hA
    apply (CatalogueBOrthogonalPointAction.mem_scalarKernel_iff_units Q _).mpr
    refine ⟨c, fun v => ?_⟩
    change (matrixNativeElementaryEquiv Q hE A).val v = (c : K) • v
    rw [matrixNativeElementaryEquiv_val, ← hc, scalarMatrixLinearEquiv]
  · intro hx
    let A := (matrixNativeElementaryEquiv Q hE).symm x
    refine ⟨A, (mem_matrixDerivedScalars_iff Q A).mpr ?_,
      (matrixNativeElementaryEquiv Q hE).apply_symm_apply x⟩
    obtain ⟨c, hc⟩ := (CatalogueBOrthogonalPointAction.mem_scalarKernel_iff_units Q x).mp hx
    refine ⟨c, ?_⟩
    have hlin : matrixLinearEquiv A.val = x.val := by
      have h := matrixNativeElementaryEquiv_val Q hE A
      rw [MulEquiv.apply_symm_apply] at h
      exact h.symm
    apply matrixLinearIso.injective
    apply LinearEquiv.ext
    intro v
    change matrixLinearEquiv (GeneralLinearGroup.scalar (Fin d) c) v = matrixLinearEquiv A.val v
    rw [scalarMatrixLinearEquiv, hlin]
    exact (hc v).symm

@[expose] def matrixNativeProjectiveEquiv (Q : QuadraticForm K (Fin d → K))
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) :
    matrixProjectiveDerived Q ≃* CatalogueBOrthogonalPointAction.ProjectiveGroup Q :=
  QuotientGroup.congr _ _ (matrixNativeElementaryEquiv Q hE)
    (matrixNativeElementaryEquiv_scalars Q hE)

theorem matrixNativeProjectiveEquiv_mk (Q : QuadraticForm K (Fin d → K))
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (A : matrixDerived Q) :
    matrixNativeProjectiveEquiv Q hE (matrixProjectiveProjection Q A) =
      QuotientGroup.mk' (CatalogueBOrthogonalPointAction.scalarKernel Q)
        (matrixNativeElementaryEquiv Q hE A) :=
  QuotientGroup.congr_mk' _ _ _ _ A

theorem derivedPointAction_native (Q : QuadraticForm K (Fin d → K))
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (A : matrixDerived Q) :
    derivedPointAction Q A = CatalogueBOrthogonalPointAction.elementaryPointAction Q
      (matrixNativeElementaryEquiv Q hE A) := by
  apply Equiv.ext
  intro L
  apply Subtype.ext
  rw [derivedPointAction_submodule]
  change _ = ((matrixNativeElementaryEquiv Q hE A) • L).val
  rw [CatalogueBOrthogonalPointAction.elementary_smul_submodule,
    matrixNativeElementaryEquiv_val]

theorem projectivePointAction_native (Q : QuadraticForm K (Fin d → K))
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (g : matrixProjectiveDerived Q) :
    projectivePointAction Q g = CatalogueBOrthogonalPointAction.projectivePointAction Q
      (matrixNativeProjectiveEquiv Q hE g) := by
  obtain ⟨A, rfl⟩ := matrixProjectiveProjection_surjective Q g
  rw [matrixNativeProjectiveEquiv_mk, projectivePointAction_mk,
    CatalogueBOrthogonalPointAction.projectivePointAction_mk]
  exact derivedPointAction_native Q hE A

theorem projectivePointAction_native_symm (Q : QuadraticForm K (Fin d → K))
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (g : CatalogueBOrthogonalPointAction.ProjectiveGroup Q) :
    CatalogueBOrthogonalPointAction.projectivePointAction Q g =
      projectivePointAction Q ((matrixNativeProjectiveEquiv Q hE).symm g) := by
  rw [projectivePointAction_native Q hE, MulEquiv.apply_symm_apply]

end CFSG.ComponentClassification.CatalogueBOrthogonalPointData
