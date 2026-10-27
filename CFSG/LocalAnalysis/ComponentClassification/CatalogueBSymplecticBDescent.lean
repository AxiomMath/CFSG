module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBDescentForm

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBSymplecticB

open CatalogueBLinearTwoDescent CatalogueBOrthogonalDescent CatalogueBAlternatingIsometry
open scoped TensorProduct

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

theorem symplecticCentralizer_normalized (B : LinearMap.BilinForm K V) (tau0 : V ≃+ V)
    (b : Kˣ) :
    semilinearSymplecticCentralizer B tau0 =
      semilinearSymplecticCentralizer B (normalizedOperator tau0 b) := by
  ext g
  rw [mem_semilinearSymplecticCentralizer_iff, mem_semilinearSymplecticCentralizer_iff]
  exact (commutes_normalized_iff tau0 b g.val.toLinearMap).symm

variable (sigma : K ≃+* K) (tau0 : V ≃+ V) (b : Kˣ)
variable (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x)
variable (B : LinearMap.BilinForm K V) (mu c : Kˣ)
variable (hform : ∀ x y, B (tau0 x) (tau0 y) = (mu : K) * sigma (B x y))
variable (hc : sigma (c : K) / (c : K) = (b : K) ^ 2 * (mu : K))
variable [Module.Finite K V]
variable (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (h2 : (2 : K) ≠ 0)
variable (lambda : Kˣ) (hsquare : ∀ x, tau0 (tau0 x) = (lambda : K) • x)
variable (hb : (b : K) * sigma (b : K) = (lambda : K)⁻¹)

@[expose] def originalSymplecticDescentEquiv :
    semilinearSymplecticCentralizer B tau0 ≃*
      isometryGroup (originalDescendedBilinear sigma tau0 b hsemi B mu c hform hc) :=
  (MulEquiv.subgroupCongr (symplecticCentralizer_normalized B tau0 b)).trans
    (symplecticFixedCentralizerEquiv sigma (normalizedOperator tau0 b)
      (normalizedOperator_semilinear sigma tau0 b hsemi) B c
      (normalized_form_identity sigma B tau0 mu b c hform hc) hsigma hne h2
      (normalizedOperator_involutive sigma tau0 lambda b hsemi hsquare hb))

theorem originalSymplecticDescentEquiv_apply (g : semilinearSymplecticCentralizer B tau0)
    (w : originalFixedSubspace sigma tau0 b hsemi) :
    ((originalSymplecticDescentEquiv sigma tau0 b hsemi B mu c hform hc hsigma hne h2 lambda
      hsquare hb g).val w : V) = g.val.val (w : V) := rfl

theorem originalSymplecticDescentEquiv_symm_apply_val_symm
    (g : semilinearSymplecticCentralizer B tau0)
    (w : originalFixedSubspace sigma tau0 b hsemi) :
    (((originalSymplecticDescentEquiv sigma tau0 b hsemi B mu c hform hc hsigma hne h2 lambda
      hsquare hb g).val).symm w : V) = g.val.val.symm (w : V) := rfl

theorem originalSymplecticDescentEquiv_symm_smul
    (f : isometryGroup (originalDescendedBilinear sigma tau0 b hsemi B mu c hform hc))
    (a : K) (w : originalFixedSubspace sigma tau0 b hsemi) :
    ((originalSymplecticDescentEquiv sigma tau0 b hsemi B mu c hform hc hsigma hne h2 lambda
      hsquare hb).symm f).val.val (a • (w : V)) = a • (f.val w : V) :=
  symplecticFixedExtension_smul sigma (normalizedOperator tau0 b)
    (normalizedOperator_semilinear sigma tau0 b hsemi) B c
    (normalized_form_identity sigma B tau0 mu b c hform hc) hsigma hne h2
    (normalizedOperator_involutive sigma tau0 lambda b hsemi hsquare hb) f a w

theorem originalSymplecticDescentEquiv_symm_inverse_smul
    (f : isometryGroup (originalDescendedBilinear sigma tau0 b hsemi B mu c hform hc))
    (a : K) (w : originalFixedSubspace sigma tau0 b hsemi) :
    ((originalSymplecticDescentEquiv sigma tau0 b hsemi B mu c hform hc hsigma hne h2 lambda
      hsquare hb).symm f).val.val.symm (a • (w : V)) = a • (f.val.symm w : V) :=
  symplecticFixedExtension_symm_smul sigma (normalizedOperator tau0 b)
    (normalizedOperator_semilinear sigma tau0 b hsemi) B c
    (normalized_form_identity sigma B tau0 mu b c hform hc) hsigma hne h2
    (normalizedOperator_involutive sigma tau0 lambda b hsemi hsquare hb) f a w

omit [Module.Finite K V] in
theorem exists_fixedSubfield_unit (hfixed : sigma (lambda : K) = (lambda : K)) :
    ∃ ell : (fixedSubfield K sigma)ˣ, ((ell : fixedSubfield K sigma) : K) = (lambda : K) := by
  let ell : fixedSubfield K sigma := ⟨(lambda : K), (mem_fixedSubfield K sigma _).mpr hfixed⟩
  have hell : ell ≠ 0 := by
    intro h
    apply Units.ne_zero lambda
    exact congrArg (fun a : fixedSubfield K sigma => (a : K)) h
  exact ⟨Units.mk0 ell hell, rfl⟩

variable [Finite K]

theorem odd_symplectic_quadratic_semilinear_descent
    (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (h2 : (2 : K) ≠ 0)
    (hdim : 0 < Module.finrank K V)
    (B : LinearMap.BilinForm K V) (hB : B.IsAlt) (hnd : B.Nondegenerate)
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
        ∀ (hc : sigma (c : K) / (c : K) = (b : K) ^ 2 * (mu : K)),
        let T := normalizedOperator tau0 b
        let W := originalFixedSubspace sigma tau0 b hsemi
        let B0 := originalDescendedBilinear sigma tau0 b hsemi B mu c hform hc
        Function.Involutive T ∧
          (∀ x, T x = (b : K) • tau0 x) ∧
          (∀ a x, T (a • x) = sigma a • T x) ∧
          (∀ x, x ∈ W ↔ (b : K) • tau0 x = x) ∧
          Module.Finite (fixedSubfield K sigma) W ∧
          Module.finrank (fixedSubfield K sigma) W = Module.finrank K V ∧
          (∀ x y : W, (B0 x y : K) = (c : K) * B (x : V) (y : V)) ∧
          B0.IsAlt ∧ B0.Nondegenerate ∧
          ∃ (j : (K ⊗[fixedSubfield K sigma] W) ≃ₗ[K] V)
            (e : semilinearSymplecticCentralizer B tau0 ≃* isometryGroup B0),
            (∀ (a : K) (w : W), j (a ⊗ₜ w) = a • (w : V)) ∧
            (∀ (a : K) (w : W), j.symm (a • (w : V)) = a ⊗ₜ w) ∧
            (∀ g (w : W), ((e g).val w : V) = g.val.val (w : V)) ∧
            (∀ g (w : W), ((e g).val.symm w : V) = g.val.val.symm (w : V)) ∧
            (∀ f (a : K) (w : W), (e.symm f).val.val (a • (w : V)) = a • (f.val w : V)) ∧
            (∀ f (a : K) (w : W),
              (e.symm f).val.val.symm (a • (w : V)) = a • (f.val.symm w : V)) := by
  let : Nontrivial V := (Module.finrank_pos_iff (R := K) (M := V)).mp hdim
  have hfixed := square_scalar_fixed sigma tau0 (lambda : K) hsemi hsquare
  have hmu := square_multiplier_identity sigma hsigma B hnd tau0 (mu : K) (lambda : K)
    hform hsquare
  refine ⟨hfixed, exists_fixedSubfield_unit sigma lambda hfixed, hmu,
    exists_normalizing_units sigma hsigma hne mu lambda hfixed hmu, ?_⟩
  intro b c hb hc
  let T := normalizedOperator tau0 b
  let hs := normalizedOperator_semilinear sigma tau0 b hsemi
  let hf := normalized_form_identity sigma B tau0 mu b c hform hc
  have hT := normalizedOperator_involutive sigma tau0 lambda b hsemi hsquare hb
  have hfinite : Module.Finite (fixedSubfield K sigma) (fixedSubspace sigma T hs) := by
    obtain ⟨e, d, hd⟩ := exists_fixedSpace_basis sigma hsigma hne h2 T hT hs
    exact Module.Finite.of_basis d
  refine ⟨hT, normalizedOperator_apply tau0 b, hs, fun x => Iff.rfl, hfinite,
    fixedSubspace_finrank sigma hsigma hne h2 T hT hs,
    descendedBilinear_apply sigma T hs B c hf,
    descendedBilinear_isAlt sigma T hs B c hf hB,
    descendedBilinear_nondegenerate_of_isAlt sigma T hs B c hf hsigma hne h2 hT hB hnd,
    scalarExtensionEquiv sigma hsigma hne h2 T hT hs,
    originalSymplecticDescentEquiv sigma tau0 b hsemi B mu c hform hc hsigma hne h2 lambda
      hsquare hb,
    scalarExtensionEquiv_tmul sigma hsigma hne h2 T hT hs,
    scalarExtensionEquiv_symm_smul sigma hsigma hne h2 T hT hs,
    originalSymplecticDescentEquiv_apply sigma tau0 b hsemi B mu c hform hc hsigma hne h2
      lambda hsquare hb,
    originalSymplecticDescentEquiv_symm_apply_val_symm sigma tau0 b hsemi B mu c hform hc
      hsigma hne h2 lambda hsquare hb,
    originalSymplecticDescentEquiv_symm_smul sigma tau0 b hsemi B mu c hform hc hsigma hne h2
      lambda hsquare hb,
    originalSymplecticDescentEquiv_symm_inverse_smul sigma tau0 b hsemi B mu c hform hc
      hsigma hne h2 lambda hsquare hb⟩

end CFSG.ComponentClassification.CatalogueBSymplecticB
