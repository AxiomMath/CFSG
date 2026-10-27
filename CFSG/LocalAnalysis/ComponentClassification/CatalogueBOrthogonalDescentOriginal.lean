module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentNormalization

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalDescent

open CatalogueBLinearTwoDescent

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

theorem orthogonalCentralizer_normalized (Q : QuadraticForm K V) (tau0 : V ≃+ V) (b : Kˣ) :
    semilinearOrthogonalCentralizer Q tau0 =
      semilinearOrthogonalCentralizer Q (normalizedOperator tau0 b) := by
  ext g
  rw [mem_semilinearOrthogonalCentralizer_iff, mem_semilinearOrthogonalCentralizer_iff]
  exact (commutes_normalized_iff tau0 b g.val.toLinearMap).symm

variable (sigma : K ≃+* K) (tau0 : V ≃+ V) (b : Kˣ)
variable (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x)

abbrev originalFixedSubspace : Submodule (fixedSubfield K sigma) V :=
  fixedSubspace sigma (normalizedOperator tau0 b)
    (normalizedOperator_semilinear sigma tau0 b hsemi)

variable (B : LinearMap.BilinForm K V) (mu c : Kˣ)
variable (hform : ∀ x y, B (tau0 x) (tau0 y) = (mu : K) * sigma (B x y))
variable (hc : sigma (c : K) / (c : K) = (b : K) ^ 2 * (mu : K))

abbrev originalDescendedBilinear :
    LinearMap.BilinForm (fixedSubfield K sigma) (originalFixedSubspace sigma tau0 b hsemi) :=
  descendedBilinear sigma (normalizedOperator tau0 b)
    (normalizedOperator_semilinear sigma tau0 b hsemi) B c
    (normalized_form_identity sigma B tau0 mu b c hform hc)

abbrev originalDescendedQuadratic :
    QuadraticForm (fixedSubfield K sigma) (originalFixedSubspace sigma tau0 b hsemi) :=
  descendedQuadratic sigma (normalizedOperator tau0 b)
    (normalizedOperator_semilinear sigma tau0 b hsemi) B c
    (normalized_form_identity sigma B tau0 mu b c hform hc)

variable [Module.Finite K V]
variable (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (h2 : (2 : K) ≠ 0)
variable (hsym : B.IsSymm) (lambda : Kˣ)
variable (hsquare : ∀ x, tau0 (tau0 x) = (lambda : K) • x)
variable (hb : (b : K) * sigma (b : K) = (lambda : K)⁻¹)

@[expose] def originalDescentCentralizerEquiv :
    semilinearOrthogonalCentralizer (originalQuadratic B) tau0 ≃*
      TauCeti.QuadraticMap.orthogonalGroup
        (originalDescendedQuadratic sigma tau0 b hsemi B mu c hform hc) :=
  (MulEquiv.subgroupCongr (orthogonalCentralizer_normalized (originalQuadratic B) tau0 b)).trans
    (orthogonalFixedCentralizerEquiv sigma hsigma hne h2 (normalizedOperator tau0 b)
      (normalizedOperator_involutive sigma tau0 lambda b hsemi hsquare hb)
      (normalizedOperator_semilinear sigma tau0 b hsemi) B hsym c
      (normalized_form_identity sigma B tau0 mu b c hform hc))

theorem originalDescentCentralizerEquiv_apply
    (g : semilinearOrthogonalCentralizer (originalQuadratic B) tau0)
    (w : originalFixedSubspace sigma tau0 b hsemi) :
    ((originalDescentCentralizerEquiv sigma tau0 b hsemi B mu c hform hc
      hsigma hne h2 hsym lambda hsquare hb g).val w : V) = g.val.val (w : V) := by
  change ((orthogonalFixedCentralizerEquiv sigma hsigma hne h2 (normalizedOperator tau0 b)
    (normalizedOperator_involutive sigma tau0 lambda b hsemi hsquare hb)
    (normalizedOperator_semilinear sigma tau0 b hsemi) B hsym c
    (normalized_form_identity sigma B tau0 mu b c hform hc)
    ((MulEquiv.subgroupCongr (orthogonalCentralizer_normalized (originalQuadratic B) tau0 b)) g)).val
    w : V) = _
  rw [orthogonalFixedCentralizerEquiv_apply]
  rw [MulEquiv.subgroupCongr_apply]

theorem originalDescentCentralizerEquiv_symm_smul
    (f : TauCeti.QuadraticMap.orthogonalGroup
      (originalDescendedQuadratic sigma tau0 b hsemi B mu c hform hc))
    (a : K) (w : originalFixedSubspace sigma tau0 b hsemi) :
    ((originalDescentCentralizerEquiv sigma tau0 b hsemi B mu c hform hc
      hsigma hne h2 hsym lambda hsquare hb).symm f).val.val (a • (w : V)) =
      a • (f.val w : V) := by
  change ((MulEquiv.subgroupCongr
    (orthogonalCentralizer_normalized (originalQuadratic B) tau0 b)).symm
    ((orthogonalFixedCentralizerEquiv sigma hsigma hne h2 (normalizedOperator tau0 b)
      (normalizedOperator_involutive sigma tau0 lambda b hsemi hsquare hb)
      (normalizedOperator_semilinear sigma tau0 b hsemi) B hsym c
      (normalized_form_identity sigma B tau0 mu b c hform hc)).symm f)).val.val _ = _
  rw [MulEquiv.subgroupCongr_symm_apply]
  exact orthogonalFixedCentralizerEquiv_symm_smul sigma hsigma hne h2 (normalizedOperator tau0 b)
    (normalizedOperator_involutive sigma tau0 lambda b hsemi hsquare hb)
    (normalizedOperator_semilinear sigma tau0 b hsemi) B hsym c
    (normalized_form_identity sigma B tau0 mu b c hform hc) f a w

theorem originalDescentCentralizerEquiv_action_symm
    (g : semilinearOrthogonalCentralizer (originalQuadratic B) tau0)
    (w : originalFixedSubspace sigma tau0 b hsemi) :
    (((originalDescentCentralizerEquiv sigma tau0 b hsemi B mu c hform hc
      hsigma hne h2 hsym lambda hsquare hb g).val).symm w : V) =
      g.val.val.symm (w : V) := by
  change ((orthogonalFixedRestriction sigma (normalizedOperator tau0 b)
    (normalizedOperator_semilinear sigma tau0 b hsemi) B hsym h2 c
    (normalized_form_identity sigma B tau0 mu b c hform hc)
    ((MulEquiv.subgroupCongr (orthogonalCentralizer_normalized (originalQuadratic B) tau0 b)) g)).val.symm
    w : V) = _
  rw [orthogonalFixedRestriction_symm_apply]
  rw [MulEquiv.subgroupCongr_apply]

theorem originalDescentCentralizerEquiv_inverse_action
    (f : TauCeti.QuadraticMap.orthogonalGroup
      (originalDescendedQuadratic sigma tau0 b hsemi B mu c hform hc))
    (a : K) (w : originalFixedSubspace sigma tau0 b hsemi) :
    ((originalDescentCentralizerEquiv sigma tau0 b hsemi B mu c hform hc
      hsigma hne h2 hsym lambda hsquare hb).symm f).val.val.symm (a • (w : V)) =
      a • (f.val.symm w : V) := by
  change ((MulEquiv.subgroupCongr
    (orthogonalCentralizer_normalized (originalQuadratic B) tau0 b)).symm
    ((orthogonalFixedCentralizerEquiv sigma hsigma hne h2 (normalizedOperator tau0 b)
      (normalizedOperator_involutive sigma tau0 lambda b hsemi hsquare hb)
      (normalizedOperator_semilinear sigma tau0 b hsemi) B hsym c
      (normalized_form_identity sigma B tau0 mu b c hform hc)).symm f)).val.val.symm _ = _
  rw [MulEquiv.subgroupCongr_symm_apply]
  exact orthogonalFixedExtension_symm_smul sigma hsigma hne h2 (normalizedOperator tau0 b)
    (normalizedOperator_involutive sigma tau0 lambda b hsemi hsquare hb)
    (normalizedOperator_semilinear sigma tau0 b hsemi) B hsym c
    (normalized_form_identity sigma B tau0 mu b c hform hc) f a w

end CFSG.ComponentClassification.CatalogueBOrthogonalDescent
