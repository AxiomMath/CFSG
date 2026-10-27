module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusCentBasic

public section

namespace CFSG.AGLEmbedding.OmegaMinusPerf

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module CFSG.AGLEmbedding.OmegaMinusCent

section Algebra

variable {R A V : Type*} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup V] [Module R V]
  (ψ : A →ₗ[R] V) (c : V →ₗ[R] A)

@[expose] def extMap (T : A →ₗ[R] A) : V →ₗ[R] V :=
  LinearMap.id + ψ ∘ₗ (T - LinearMap.id) ∘ₗ c

variable {ψ c}

theorem extMap_apply (T : A →ₗ[R] A) (v : V) :
    extMap ψ c T v = v + (ψ (T (c v)) - ψ (c v)) := by
  simp [extMap, map_sub]

theorem c_extMap (hcψ : c ∘ₗ ψ = LinearMap.id) (T : A →ₗ[R] A) (v : V) :
    c (extMap ψ c T v) = T (c v) := by
  have h : ∀ a, c (ψ a) = a := fun a => LinearMap.congr_fun hcψ a
  rw [extMap_apply, map_add, map_sub, h, h]
  abel

theorem extMap_one : extMap ψ c (LinearMap.id : A →ₗ[R] A) = LinearMap.id := by
  ext v
  simp [extMap_apply]

theorem extMap_comp (hcψ : c ∘ₗ ψ = LinearMap.id) (S T : A →ₗ[R] A) :
    extMap ψ c (S ∘ₗ T) = extMap ψ c S ∘ₗ extMap ψ c T := by
  ext v
  rw [LinearMap.comp_apply, extMap_apply S (extMap ψ c T v), c_extMap hcψ T v, extMap_apply T v,
    extMap_apply (S ∘ₗ T) v, LinearMap.comp_apply]
  abel

@[expose] def extEquiv (hcψ : c ∘ₗ ψ = LinearMap.id) (T : A ≃ₗ[R] A) : V ≃ₗ[R] V :=
  LinearEquiv.ofLinearMap (extMap ψ c T.toLinearMap) (extMap ψ c T.symm.toLinearMap)
    (by
      rw [← extMap_comp hcψ]
      have : T.toLinearMap ∘ₗ T.symm.toLinearMap = LinearMap.id := by ext a; simp
      rw [this, extMap_one])
    (by
      rw [← extMap_comp hcψ]
      have : T.symm.toLinearMap ∘ₗ T.toLinearMap = LinearMap.id := by ext a; simp
      rw [this, extMap_one])

theorem extEquiv_apply (hcψ : c ∘ₗ ψ = LinearMap.id) (T : A ≃ₗ[R] A) (v : V) :
    extEquiv hcψ T v = v + (ψ (T (c v)) - ψ (c v)) :=
  extMap_apply _ _

@[expose] def extHom (hcψ : c ∘ₗ ψ = LinearMap.id) : (A ≃ₗ[R] A) →* (V ≃ₗ[R] V) where
  toFun := extEquiv hcψ
  map_one' := by
    apply LinearEquiv.ext
    intro v
    rw [extEquiv_apply]
    simp
  map_mul' S T := by
    apply LinearEquiv.ext
    intro v
    change extMap ψ c (S.toLinearMap ∘ₗ T.toLinearMap) v =
      extMap ψ c S.toLinearMap (extMap ψ c T.toLinearMap v)
    rw [extMap_comp hcψ]
    rfl

theorem extHom_apply (hcψ : c ∘ₗ ψ = LinearMap.id) (T : A ≃ₗ[R] A) :
    extHom hcψ T = extEquiv hcψ T :=
  rfl

end Algebra

section Quadratic

variable {A V : Type*} [AddCommGroup A] [Module (ZMod 2) A] [AddCommGroup V]
  [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {ψ : A →ₗ[ZMod 2] V}
  {c : V →ₗ[ZMod 2] A}

theorem neg_eq_self_zmod_two {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (w : W) :
    -w = w :=
  neg_eq_of_add_eq_zero_right (add_self_eq_zero' w)

theorem extEquiv_apply' (hcψ : c ∘ₗ ψ = LinearMap.id) (T : A ≃ₗ[ZMod 2] A) (v : V) :
    extEquiv hcψ T v = (v + ψ (c v)) + ψ (T (c v)) := by
  rw [extEquiv_apply, sub_eq_add_neg, neg_eq_self_zmod_two]
  abel

theorem extEquiv_mem_orthogonalGroup (hcψ : c ∘ₗ ψ = LinearMap.id)
    (hort : ∀ v a, polar Q (v + ψ (c v)) (ψ a) = 0) {T : A ≃ₗ[ZMod 2] A}
    (hT : ∀ a, Q (ψ (T a)) = Q (ψ a)) :
    extEquiv hcψ T ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  have h2 : v = (v + ψ (c v)) + ψ (c v) := by
    rw [add_assoc, add_self_eq_zero', add_zero]
  rw [extEquiv_apply', QuadraticMap.map_add Q, hort v (T (c v)), hT]
  conv_rhs => rw [h2, QuadraticMap.map_add Q, hort v (c v)]

theorem extEquiv_commute (hcψ : c ∘ₗ ψ = LinearMap.id) {x : V ≃ₗ[ZMod 2] V}
    {τ T : A ≃ₗ[ZMod 2] A} (hψ : ∀ a, x (ψ a) = ψ (τ a)) (hc : ∀ v, c (x v) = τ (c v))
    (hTτ : ∀ a, T (τ a) = τ (T a)) : x * extEquiv hcψ T = extEquiv hcψ T * x := by
  apply LinearEquiv.ext
  intro v
  change x (extEquiv hcψ T v) = extEquiv hcψ T (x v)
  rw [extEquiv_apply, extEquiv_apply, map_add, map_sub, hψ, hψ, hc, hTτ]

end Quadratic

end CFSG.AGLEmbedding.OmegaMinusPerf
