module

public import Mathlib.LinearAlgebra.Matrix.Rank

public section

namespace CFSG.ClassicalGroups.Symplectic

open Matrix

variable {K : Type*} [Field K] {E : Type*} [AddCommGroup E] [Module K E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem map_sub_one_eq_map_range {W : Submodule K E} (e : W ≃ₗ[K] (ι → K))
    (T : E →ₗ[K] E) (hT : ∀ w ∈ W, T w ∈ W) (t : Matrix ι ι K)
    (he : ∀ w : W, e ⟨T w, hT w w.2⟩ = t *ᵥ e w) :
    Submodule.map (T - 1) W =
      Submodule.map (W.subtype ∘ₗ e.symm.toLinearMap)
        (LinearMap.range (Matrix.mulVecLin (t - 1))) := by
  have hcomm : ∀ v : ι → K, T ((e.symm v : W) : E) = ((e.symm (t *ᵥ v) : W) : E) := by
    intro v
    have h1 := he (e.symm v)
    rw [LinearEquiv.apply_symm_apply] at h1
    have h2 : (⟨T (e.symm v : W), hT _ (e.symm v).2⟩ : W) = e.symm (t *ᵥ v) := by
      apply e.injective
      rw [h1, LinearEquiv.apply_symm_apply]
    exact congrArg Subtype.val h2
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨(t - 1) *ᵥ e ⟨w, hw⟩, ⟨e ⟨w, hw⟩, rfl⟩, ?_⟩
    show ((e.symm ((t - 1) *ᵥ e ⟨w, hw⟩) : W) : E) = (T - 1) w
    have h1 : ((e.symm ((t - 1) *ᵥ e ⟨w, hw⟩) : W) : E) =
        ((e.symm (t *ᵥ e ⟨w, hw⟩) : W) : E) - ((e.symm (e ⟨w, hw⟩) : W) : E) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, map_sub]
      rfl
    rw [h1, ← hcomm, LinearEquiv.symm_apply_apply]
    simp
  · rintro ⟨v, ⟨v', rfl⟩, rfl⟩
    refine ⟨((e.symm v' : W) : E), (e.symm v').2, ?_⟩
    show (T - 1) ((e.symm v' : W) : E) = ((e.symm ((t - 1) *ᵥ v') : W) : E)
    have h1 : ((e.symm ((t - 1) *ᵥ v') : W) : E) =
        ((e.symm (t *ᵥ v') : W) : E) - ((e.symm v' : W) : E) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, map_sub]
      rfl
    rw [h1, ← hcomm]
    simp

theorem finrank_map_sub_one_of_coords {W : Submodule K E} (e : W ≃ₗ[K] (ι → K))
    (T : E →ₗ[K] E) (hT : ∀ w ∈ W, T w ∈ W) (t : Matrix ι ι K)
    (he : ∀ w : W, e ⟨T w, hT w w.2⟩ = t *ᵥ e w) :
    Module.finrank K (Submodule.map (T - 1) W) = (t - 1).rank := by
  rw [map_sub_one_eq_map_range e T hT t he]
  have hinj : Function.Injective (W.subtype ∘ₗ e.symm.toLinearMap) :=
    W.injective_subtype.comp e.symm.injective
  exact (LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective (W.subtype ∘ₗ e.symm.toLinearMap) hinj
      (LinearMap.range (Matrix.mulVecLin (t - 1))))).symm

theorem finrank_map_sub_one_sup_of_coords {W₁ W₂ : Submodule K E} (hdisj : Disjoint W₁ W₂)
    (e₁ : W₁ ≃ₗ[K] (ι → K)) (e₂ : W₂ ≃ₗ[K] (ι → K)) (T : E →ₗ[K] E)
    (hT₁ : ∀ w ∈ W₁, T w ∈ W₁) (hT₂ : ∀ w ∈ W₂, T w ∈ W₂) (t : Matrix ι ι K)
    (he₁ : ∀ w : W₁, e₁ ⟨T w, hT₁ w w.2⟩ = t *ᵥ e₁ w)
    (he₂ : ∀ w : W₂, e₂ ⟨T w, hT₂ w w.2⟩ = t *ᵥ e₂ w) :
    Module.finrank K (Submodule.map (T - 1) (W₁ ⊔ W₂)) = 2 * (t - 1).rank := by
  have hle : ∀ {W : Submodule K E}, (∀ w ∈ W, T w ∈ W) →
      Submodule.map (T - 1) W ≤ W := by
    intro W hW
    rintro _ ⟨w, hw, rfl⟩
    simp only [LinearMap.sub_apply, Module.End.one_apply]
    exact W.sub_mem (hW w hw) hw
  have h1 := finrank_map_sub_one_of_coords e₁ T hT₁ t he₁
  have h2 := finrank_map_sub_one_of_coords e₂ T hT₂ t he₂
  haveI : FiniteDimensional K (Submodule.map (T - 1) W₁) := by
    rw [map_sub_one_eq_map_range e₁ T hT₁ t he₁]
    infer_instance
  haveI : FiniteDimensional K (Submodule.map (T - 1) W₂) := by
    rw [map_sub_one_eq_map_range e₂ T hT₂ t he₂]
    infer_instance
  have hd : Disjoint (Submodule.map (T - 1) W₁) (Submodule.map (T - 1) W₂) :=
    hdisj.mono (hle hT₁) (hle hT₂)
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.map (T - 1) W₁)
    (Submodule.map (T - 1) W₂)
  rw [disjoint_iff.mp hd, finrank_bot, add_zero, h1, h2] at h3
  rw [Submodule.map_sup, h3]
  ring

theorem map_sub_one_eq_span_of_range {W : Submodule K E} (e : W ≃ₗ[K] (ι → K))
    (T : E →ₗ[K] E) (hT : ∀ w ∈ W, T w ∈ W) (t : Matrix ι ι K)
    (he : ∀ w : W, e ⟨T w, hT w w.2⟩ = t *ᵥ e w) {u : ι → K}
    (hu : LinearMap.range (Matrix.mulVecLin (t - 1)) = Submodule.span K {u}) :
    Submodule.map (T - 1) W = Submodule.span K {((e.symm u : W) : E)} := by
  rw [map_sub_one_eq_map_range e T hT t he, hu, Submodule.map_span, Set.image_singleton]
  rfl

theorem smul_of_map_sub_one {W : Submodule K E} (e : W ≃ₗ[K] (ι → K))
    (T : E →ₗ[K] E) (hT : ∀ w ∈ W, T w ∈ W) (t : Matrix ι ι K)
    (he : ∀ w : W, e ⟨T w, hT w w.2⟩ = t *ᵥ e w) (S : E →ₗ[K] E) (hS : ∀ w ∈ W, S w ∈ W)
    (g : Matrix ι ι K) (heS : ∀ w : W, e ⟨S w, hS w w.2⟩ = g *ᵥ e w) (c : K)
    (hfix : ∀ v ∈ LinearMap.range (Matrix.mulVecLin (t - 1)), g *ᵥ v = c • v) :
    ∀ x ∈ Submodule.map (T - 1) W, S x = c • x := by
  intro x hx
  rw [map_sub_one_eq_map_range e T hT t he] at hx
  obtain ⟨v, hv, rfl⟩ := hx
  have h1 : S ((e.symm v : W) : E) = ((e.symm (g *ᵥ v) : W) : E) := by
    have h2 := heS (e.symm v)
    rw [LinearEquiv.apply_symm_apply] at h2
    have h3 : (⟨S (e.symm v : W), hS _ (e.symm v).2⟩ : W) = e.symm (g *ᵥ v) := by
      apply e.injective
      rw [h2, LinearEquiv.apply_symm_apply]
    exact congrArg Subtype.val h3
  show S ((e.symm v : W) : E) = c • ((e.symm v : W) : E)
  rw [h1, hfix v hv, map_smul]
  rfl

end CFSG.ClassicalGroups.Symplectic
