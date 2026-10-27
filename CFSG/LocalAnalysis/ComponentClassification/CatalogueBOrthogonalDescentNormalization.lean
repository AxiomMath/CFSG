module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryNorm

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalDescent

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

@[expose] def normalizedOperator (tau0 : V ≃+ V) (b : Kˣ) : V ≃+ V :=
  tau0.trans (LinearEquiv.smulOfUnit b).toAddEquiv

theorem normalizedOperator_apply (tau0 : V ≃+ V) (b : Kˣ) (x : V) :
    normalizedOperator tau0 b x = (b : K) • tau0 x := rfl

theorem square_scalar_fixed [Nontrivial V] (sigma : K ≃+* K) (tau0 : V ≃+ V)
    (lambda : K) (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x)
    (hsquare : ∀ x, tau0 (tau0 x) = lambda • x) : sigma lambda = lambda := by
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have ht : tau0 x ≠ 0 := by
    intro h
    apply hx
    apply tau0.injective
    simpa only [map_zero] using h
  apply smul_left_injective K ht
  calc
    sigma lambda • tau0 x = tau0 (lambda • x) := (hsemi lambda x).symm
    _ = tau0 (tau0 (tau0 x)) := congrArg tau0 (hsquare x).symm
    _ = lambda • tau0 x := hsquare (tau0 x)

theorem square_multiplier_identity [Nontrivial V] (sigma : K ≃+* K)
    (hsigma : sigma ^ 2 = 1) (B : LinearMap.BilinForm K V) (hnd : B.Nondegenerate)
    (tau0 : V ≃+ V) (mu lambda : K)
    (hform : ∀ x y, B (tau0 x) (tau0 y) = mu * sigma (B x y))
    (hsquare : ∀ x, tau0 (tau0 x) = lambda • x) :
    mu * sigma mu = lambda ^ 2 := by
  have hex : ∃ x y, B x y ≠ 0 := by
    by_contra! h
    apply LinearMap.BilinForm.Nondegenerate.ne_zero hnd
    ext x y
    exact h x y
  obtain ⟨x, y, hxy⟩ := hex
  have h := hform (tau0 x) (tau0 y)
  rw [hsquare, hsquare, hform, map_mul,
    CatalogueBUnitaryNorm.involutive sigma hsigma] at h
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  apply mul_right_cancel₀ hxy
  calc
    (mu * sigma mu) * B x y = mu * (sigma mu * B x y) := by ring
    _ = lambda * (lambda * B x y) := h.symm
    _ = lambda ^ 2 * B x y := by ring

theorem normalized_multiplier_norm (sigma : K ≃+* K) (mu lambda : Kˣ) (b : Kˣ)
    (hmu : (mu : K) * sigma (mu : K) = (lambda : K) ^ 2)
    (hb : (b : K) * sigma (b : K) = (lambda : K)⁻¹) :
    ((b : K) ^ 2 * (mu : K)) * sigma ((b : K) ^ 2 * (mu : K)) = 1 := by
  calc
    ((b : K) ^ 2 * (mu : K)) * sigma ((b : K) ^ 2 * (mu : K)) =
        ((b : K) * sigma (b : K)) ^ 2 * ((mu : K) * sigma (mu : K)) := by
      rw [map_mul, map_pow]
      ring
    _ = (lambda : K)⁻¹ ^ 2 * (lambda : K) ^ 2 := by rw [hb, hmu]
    _ = 1 := by field_simp

theorem exists_normalizing_units [Finite K] (sigma : K ≃+* K)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (mu lambda : Kˣ)
    (hfixed : sigma (lambda : K) = (lambda : K))
    (hmu : (mu : K) * sigma (mu : K) = (lambda : K) ^ 2) :
    ∃ b c : Kˣ, (b : K) * sigma (b : K) = (lambda : K)⁻¹ ∧
      sigma (c : K) / (c : K) = (b : K) ^ 2 * (mu : K) := by
  obtain ⟨b, hb⟩ := CatalogueBLinearTwoDescent.exists_norm_unit K sigma hsigma hne
    lambda⁻¹ (by
      simpa only [Units.val_inv_eq_inv_val, map_inv₀] using
        congrArg (fun a : K => a⁻¹) hfixed)
  have hb' : (b : K) * sigma (b : K) = (lambda : K)⁻¹ := by
    simpa only [Units.val_inv_eq_inv_val] using hb
  let eta : Kˣ := b ^ 2 * mu
  have heta : sigma (eta : K) * (eta : K) = 1 := by
    change sigma ((b : K) ^ 2 * (mu : K)) * ((b : K) ^ 2 * (mu : K)) = 1
    rw [mul_comm]
    exact normalized_multiplier_norm sigma mu lambda b hmu hb'
  obtain ⟨d, hd⟩ := CatalogueBUnitaryNorm.exists_norm_one_ratio sigma hsigma hne eta heta
  change (d : K) / sigma (d : K) = (b : K) ^ 2 * (mu : K) at hd
  refine ⟨b, d⁻¹, hb', ?_⟩
  simpa only [Units.val_inv_eq_inv_val, map_inv₀, inv_div_inv] using hd

theorem normalizedOperator_involutive (sigma : K ≃+* K) (tau0 : V ≃+ V)
    (lambda b : Kˣ) (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x)
    (hsquare : ∀ x, tau0 (tau0 x) = (lambda : K) • x)
    (hb : (b : K) * sigma (b : K) = (lambda : K)⁻¹) :
    Function.Involutive (normalizedOperator tau0 b) := by
  intro x
  rw [normalizedOperator_apply, normalizedOperator_apply, hsemi, hsquare]
  rw [smul_smul, smul_smul, hb, inv_mul_cancel₀ (Units.ne_zero lambda), one_smul]

theorem normalizedOperator_semilinear (sigma : K ≃+* K) (tau0 : V ≃+ V) (b : Kˣ)
    (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x) (a : K) (x : V) :
    normalizedOperator tau0 b (a • x) = sigma a • normalizedOperator tau0 b x := by
  simp only [normalizedOperator_apply, hsemi, smul_smul]
  rw [mul_comm]

theorem normalized_form_identity (sigma : K ≃+* K) (B : LinearMap.BilinForm K V)
    (tau0 : V ≃+ V) (mu b c : Kˣ)
    (hform : ∀ x y, B (tau0 x) (tau0 y) = (mu : K) * sigma (B x y))
    (hc : sigma (c : K) / (c : K) = (b : K) ^ 2 * (mu : K)) (x y : V) :
    (c : K) * B (normalizedOperator tau0 b x) (normalizedOperator tau0 b y) =
      sigma ((c : K) * B x y) := by
  have hc' : sigma (c : K) = ((b : K) ^ 2 * (mu : K)) * (c : K) :=
    (div_eq_iff (Units.ne_zero c)).mp hc
  simp only [normalizedOperator_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    hform, map_mul, hc']
  ring

theorem commutes_normalized_iff (tau0 : V ≃+ V) (b : Kˣ) (g : V →ₗ[K] V) :
    (∀ x, g (normalizedOperator tau0 b x) = normalizedOperator tau0 b (g x)) ↔
      ∀ x, g (tau0 x) = tau0 (g x) := by
  simp only [normalizedOperator_apply, map_smul]
  constructor
  · intro h x
    exact (smul_right_injective V (Units.ne_zero b)) (h x)
  · intro h x
    rw [h]

end CFSG.ComponentClassification.CatalogueBOrthogonalDescent
