module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentOriginal

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalDescent

open CatalogueBLinearTwoDescent
open scoped TensorProduct

universe u v

variable {K : Type u} [Field K] [Finite K]
variable {V : Type v} [AddCommGroup V] [Module K V] [Module.Finite K V]

theorem odd_orthogonal_quadratic_semilinear_descent
    (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (h2 : (2 : K) ≠ 0)
    (hdim : 0 < Module.finrank K V)
    (B : LinearMap.BilinForm K V) (hsym : B.IsSymm) (hnd : B.Nondegenerate)
    (tau0 : V ≃+ V) (mu lambda : Kˣ)
    (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x)
    (hform : ∀ x y, B (tau0 x) (tau0 y) = (mu : K) * sigma (B x y))
    (hsquare : ∀ x, tau0 (tau0 x) = (lambda : K) • x) :
    sigma (lambda : K) = (lambda : K) ∧
      (∃ ell : (fixedSubfield K sigma)ˣ,
        ((ell : fixedSubfield K sigma) : K) = (lambda : K)) ∧
      (mu : K) * sigma (mu : K) = (lambda : K) ^ 2 ∧
      (∃ b c : Kˣ, (b : K) * sigma (b : K) = (lambda : K)⁻¹ ∧
        sigma (c : K) / (c : K) = (b : K) ^ 2 * (mu : K)) ∧
      ∀ (b c : Kˣ), (b : K) * sigma (b : K) = (lambda : K)⁻¹ →
        ∀
        (hc : sigma (c : K) / (c : K) = (b : K) ^ 2 * (mu : K)),
        let T := normalizedOperator tau0 b
        let W := originalFixedSubspace sigma tau0 b hsemi
        let B0 := originalDescendedBilinear sigma tau0 b hsemi B mu c hform hc
        let Q0 := originalDescendedQuadratic sigma tau0 b hsemi B mu c hform hc
        Function.Involutive T ∧
          (∀ x, T x = (b : K) • tau0 x) ∧
          (∀ a x, T (a • x) = sigma a • T x) ∧
          (∀ x, x ∈ W ↔ (b : K) • tau0 x = x) ∧
          Module.Finite (fixedSubfield K sigma) W ∧
          Module.finrank (fixedSubfield K sigma) W = Module.finrank K V ∧
          B0.IsSymm ∧ B0.Nondegenerate ∧
          (∀ x y : W, (B0 x y : K) = (c : K) * B (x : V) (y : V)) ∧
          (∀ x : W, Q0 x = B0 x x / 2) ∧
          Q0.polarBilin = B0 ∧
          (∀ x : W, (Q0 x : K) = (c : K) * originalQuadratic B (x : V)) ∧
          ∃ (j : (K ⊗[fixedSubfield K sigma] W) ≃ₗ[K] V)
            (e : semilinearOrthogonalCentralizer (originalQuadratic B) tau0 ≃*
              TauCeti.QuadraticMap.orthogonalGroup Q0),
            (∀ (a : K) (w : W), j (a ⊗ₜ w) = a • (w : V)) ∧
            (∀ (a : K) (w : W), j.symm (a • (w : V)) = a ⊗ₜ w) ∧
            (∀ g (w : W), ((e g).val w : V) = g.val.val (w : V)) ∧
            (∀ g (w : W), ((e g).val.symm w : V) = g.val.val.symm (w : V)) ∧
            (∀ f (a : K) (w : W), (e.symm f).val.val (a • (w : V)) = a • (f.val w : V)) ∧
            (∀ f (a : K) (w : W), (e.symm f).val.val.symm (a • (w : V)) = a • (f.val.symm w : V)) ∧
            (∀ g, e.symm (e g) = g) ∧ (∀ f, e (e.symm f) = f) := by
  let : Nontrivial V := (Module.finrank_pos_iff (R := K) (M := V)).mp hdim
  have hfixed := square_scalar_fixed sigma tau0 (lambda : K) hsemi hsquare
  have hmu := square_multiplier_identity sigma hsigma B hnd tau0 (mu : K) (lambda : K)
    hform hsquare
  refine ⟨hfixed, ?_, hmu, exists_normalizing_units sigma hsigma hne mu lambda hfixed hmu, ?_⟩
  · let ell : fixedSubfield K sigma :=
      ⟨(lambda : K), (mem_fixedSubfield K sigma _).mpr hfixed⟩
    have hell : ell ≠ 0 := by
      intro h
      apply Units.ne_zero lambda
      exact congrArg (fun a : fixedSubfield K sigma => (a : K)) h
    exact ⟨Units.mk0 ell hell, rfl⟩
  · intro b c hb hc
    let T := normalizedOperator tau0 b
    let hs := normalizedOperator_semilinear sigma tau0 b hsemi
    let hf := normalized_form_identity sigma B tau0 mu b c hform hc
    have hT := normalizedOperator_involutive sigma tau0 lambda b hsemi hsquare hb
    have hfinite : Module.Finite (fixedSubfield K sigma) (fixedSubspace sigma T hs) := by
      obtain ⟨e, d, hd⟩ := exists_fixedSpace_basis sigma hsigma hne h2 T hT hs
      exact Module.Finite.of_basis d
    refine ⟨hT, normalizedOperator_apply tau0 b, hs, ?_, hfinite,
      fixedSubspace_finrank sigma hsigma hne h2 T hT hs,
      descendedBilinear_isSymm sigma T hs B c hf hsym,
      descendedBilinear_nondegenerate sigma T hs B c hf hsigma hne h2 hT hsym hnd,
      descendedBilinear_apply sigma T hs B c hf,
      descendedQuadratic_apply sigma T hs B c hf,
      descendedQuadratic_polarBilin sigma T hs B c hf hsym h2,
      descendedQuadratic_original_apply sigma T hs B c hf, ?_⟩
    · intro x
      exact Iff.rfl
    · refine ⟨scalarExtensionEquiv sigma hsigma hne h2 T hT hs,
        originalDescentCentralizerEquiv sigma tau0 b hsemi B mu c hform hc
          hsigma hne h2 hsym lambda hsquare hb,
        scalarExtensionEquiv_tmul sigma hsigma hne h2 T hT hs,
        scalarExtensionEquiv_symm_smul sigma hsigma hne h2 T hT hs,
        originalDescentCentralizerEquiv_apply sigma tau0 b hsemi B mu c hform hc
          hsigma hne h2 hsym lambda hsquare hb,
        originalDescentCentralizerEquiv_action_symm sigma tau0 b hsemi B mu c hform hc
          hsigma hne h2 hsym lambda hsquare hb,
        originalDescentCentralizerEquiv_symm_smul sigma tau0 b hsemi B mu c hform hc
          hsigma hne h2 hsym lambda hsquare hb,
        originalDescentCentralizerEquiv_inverse_action sigma tau0 b hsemi B mu c hform hc
          hsigma hne h2 hsym lambda hsquare hb, ?_, ?_⟩
      · exact fun g => MulEquiv.symm_apply_apply _ g
      · exact fun f => MulEquiv.apply_symm_apply _ f

end CFSG.ComponentClassification.CatalogueBOrthogonalDescent
