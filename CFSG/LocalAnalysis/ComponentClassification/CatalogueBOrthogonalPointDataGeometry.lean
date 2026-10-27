module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataNative
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointKernelProjective
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataNormalizer

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointData

open CatalogueBOrthogonalSemilinear
open QuadraticMap CFSG.ClassicalGroups.Orthogonal
open scoped Classical

universe u

variable {K : Type u} [Field K] {d : ℕ}

theorem projectivePointStabilizer_eq_actionStabilizer
    (Q : QuadraticForm K (Fin d → K)) (L : CatalogueBOrthogonalPointAction.Points Q) :
    projectivePointStabilizer Q L =
      CatalogueBOrthogonalPointAction.actionStabilizer Q (projectivePointAction Q) L := by
  ext g
  rfl

theorem projective_point_action_properties (Q : QuadraticForm K (Fin d → K))
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧
      ∀ x ∈ T, Q x = 0) :
    CatalogueBOrthogonalPointAction.ActionProperties Q (projectivePointAction Q) :=
  CatalogueBOrthogonalPointAction.actionProperties_equiv Q _ _
    (matrixNativeProjectiveEquiv Q hE) (projectivePointAction_native Q hE)
    (CatalogueBOrthogonalPointAction.projective_action_properties Q hQ hT)

theorem projectivePointStabilizer_injective_native (Q : QuadraticForm K (Fin d → K))
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧
      ∀ x ∈ T, Q x = 0) :
    Function.Injective (projectivePointStabilizer Q) := by
  have h := (projective_point_action_properties Q hE hQ hT).2.2.2.2.2.1
  intro L M hLM
  apply h
  simpa only [← projectivePointStabilizer_eq_actionStabilizer] using hLM

theorem projective_point_stabilizer_orbits (Q : QuadraticForm K (Fin d → K))
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧
      ∀ x ∈ T, Q x = 0) (L M : CatalogueBOrthogonalPointAction.Points Q) :
    CatalogueBOrthogonalPointAction.actionStabilizerOrbit Q (projectivePointAction Q) L M =
      if M = L then {L} else if CatalogueBOrthogonalPointAction.PointPerp L M then
        CatalogueBOrthogonalPointAction.perpendicularPoints Q L else
        CatalogueBOrthogonalPointAction.nonperpendicularPoints Q L :=
  (projective_point_action_properties Q hE hQ hT).2.2.2.2.2.2.1 L M

theorem projective_point_off_diagonal (Q : QuadraticForm K (Fin d → K))
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧
      ∀ x ∈ T, Q x = 0) (L : CatalogueBOrthogonalPointAction.Points Q) :
    (∃ M N : CatalogueBOrthogonalPointAction.Points Q, M ≠ N ∧
      M ∈ CatalogueBOrthogonalPointAction.perpendicularPoints Q L ∧
      N ∈ CatalogueBOrthogonalPointAction.perpendicularPoints Q L) ∧
    (∃ M N : CatalogueBOrthogonalPointAction.Points Q, M ≠ N ∧
      M ∈ CatalogueBOrthogonalPointAction.nonperpendicularPoints Q L ∧
      N ∈ CatalogueBOrthogonalPointAction.nonperpendicularPoints Q L) :=
  (projective_point_action_properties Q hE hQ hT).2.2.2.2.2.2.2 L

@[expose] def nativePointFamilyNormalizerEquiv (Q : QuadraticForm K (Fin d → K))
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧
      ∀ x ∈ T, Q x = 0) :
    projectivePointFamilyAut Q ≃* projectivePointNormalizer Q :=
  pointFamilyNormalizerEquiv Q
    (CatalogueBOrthogonalPointKernel.projectivePointAction_injective Q hQ hT)
    (projectivePointStabilizer_injective_native Q hE hQ hT)

theorem nativePointFamilyNormalizerEquiv_stabilizer (Q : QuadraticForm K (Fin d → K))
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧
      ∀ x ∈ T, Q x = 0) (alpha : projectivePointFamilyAut Q)
    (L : CatalogueBOrthogonalPointAction.Points Q) :
    (projectivePointStabilizer Q L).map alpha.val.toMonoidHom =
      projectivePointStabilizer Q ((nativePointFamilyNormalizerEquiv Q hE hQ hT alpha).val L) :=
  pointFamilyNormalizerEquiv_stabilizer Q _ _ alpha L

theorem nativePointFamilyNormalizerEquiv_covariance (Q : QuadraticForm K (Fin d → K))
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧
      ∀ x ∈ T, Q x = 0) (alpha : projectivePointFamilyAut Q)
    (x : matrixProjectiveDerived Q) :
    (nativePointFamilyNormalizerEquiv Q hE hQ hT alpha).val * projectivePointAction Q x *
        (nativePointFamilyNormalizerEquiv Q hE hQ hT alpha).val⁻¹ =
      projectivePointAction Q (alpha.val x) :=
  pointFamilyNormalizerEquiv_covariance Q _ _ alpha x

end CFSG.ComponentClassification.CatalogueBOrthogonalPointData
