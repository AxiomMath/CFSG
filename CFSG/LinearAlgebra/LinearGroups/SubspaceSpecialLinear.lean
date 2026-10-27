module

public import Mathlib.LinearAlgebra.SpecialLinearGroup

public section

namespace Submodule

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable def specialLinearEmbedding (E P : Submodule K V) (h : IsCompl E P) :
    SpecialLinearGroup K E →* (V ≃ₗ[K] V) where
  toFun g :=
    let e := prodEquivOfIsCompl E P h
    (e.symm.trans ((g : E ≃ₗ[K] E).prodCongr (LinearEquiv.refl K P))).trans e
  map_one' := by
    ext v
    change (prodEquivOfIsCompl E P h) ((prodEquivOfIsCompl E P h).symm v) = v
    exact (prodEquivOfIsCompl E P h).apply_symm_apply v
  map_mul' := by
    intro g g'
    ext v
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.prodCongr_apply, SpecialLinearGroup.coe_mul, LinearEquiv.mul_apply,
      LinearEquiv.refl_apply, Prod.fst, Prod.snd]

@[simp] theorem specialLinearEmbedding_apply_add {E P : Submodule K V} (h : IsCompl E P)
    (g : SpecialLinearGroup K E) (x : E) (y : P) :
    specialLinearEmbedding E P h g ((x : V) + (y : V)) = (g x : V) + (y : V) := by
  let e := prodEquivOfIsCompl E P h
  have hxy : e.symm ((x : V) + (y : V)) = (x, y) := e.symm_apply_eq.mpr rfl
  change e (((g : E ≃ₗ[K] E).prodCongr (LinearEquiv.refl K P))
    (e.symm ((x : V) + (y : V)))) = (g x : V) + (y : V)
  rw [hxy]
  rfl

@[simp] theorem specialLinearEmbedding_apply_left {E P : Submodule K V} (h : IsCompl E P)
    (g : SpecialLinearGroup K E) (x : E) :
    specialLinearEmbedding E P h g (x : V) = (g x : V) := by
  simpa using specialLinearEmbedding_apply_add h g x 0

@[simp] theorem specialLinearEmbedding_apply_right {E P : Submodule K V} (h : IsCompl E P)
    (g : SpecialLinearGroup K E) (x : P) :
    specialLinearEmbedding E P h g (x : V) = (x : V) := by
  simpa using specialLinearEmbedding_apply_add h g 0 x

theorem specialLinearEmbedding_injective {E P : Submodule K V} (h : IsCompl E P) :
    Function.Injective (specialLinearEmbedding E P h) := by
  intro g g' hgg
  apply SpecialLinearGroup.ext
  intro x
  apply Subtype.ext
  have hx := congrArg (fun f : V ≃ₗ[K] V => f (x : V)) hgg
  simpa using hx

theorem det_specialLinearEmbedding [FiniteDimensional K V]
    {E P : Submodule K V} (h : IsCompl E P) (g : SpecialLinearGroup K E) :
    LinearMap.det (specialLinearEmbedding E P h g).toLinearMap = 1 := by
  let e := prodEquivOfIsCompl E P h
  change LinearMap.det (e.toLinearMap.comp
    ((LinearMap.prodMap (g : E →ₗ[K] E) LinearMap.id).comp e.symm.toLinearMap)) = 1
  rw [LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_id, mul_one]
  exact SpecialLinearGroup.det_eq_one g

theorem mem_range_specialLinearEmbedding_of_det_eq_one [FiniteDimensional K V]
    {E P : Submodule K V} (h : IsCompl E P) (f : V ≃ₗ[K] V)
    (hdet : LinearMap.det f.toLinearMap = 1)
    (hP : ∀ x ∈ P, f x = x)
    (hE : ∀ x ∈ E, f x ∈ E) (hE' : ∀ x ∈ E, f.symm x ∈ E) :
    f ∈ (specialLinearEmbedding E P h).range := by
  have hmap : E.map f.toLinearMap = E := by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact hE y hy
    · intro x hx
      exact ⟨f.symm x, hE' x hx, f.apply_symm_apply x⟩
  let g : E ≃ₗ[K] E := f.ofSubmodules E E hmap
  let e := prodEquivOfIsCompl E P h
  have heq : f = (e.symm.trans (g.prodCongr (LinearEquiv.refl K P))).trans e := by
    apply LinearEquiv.ext
    intro v
    obtain ⟨⟨x, y⟩, rfl⟩ := e.surjective v
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply]
    change f ((x : V) + (y : V)) = f x + (y : V)
    rw [map_add, hP y y.property]
  have hdetg : LinearMap.det g.toLinearMap = 1 := by
    rw [heq] at hdet
    change LinearMap.det (e.toLinearMap.comp
      ((LinearMap.prodMap g.toLinearMap LinearMap.id).comp e.symm.toLinearMap)) = 1 at hdet
    rw [LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_id, mul_one] at hdet
    exact hdet
  let gSL : SpecialLinearGroup K E := ⟨g, by
    apply Units.ext
    simpa only [LinearEquiv.coe_det, Units.val_one] using hdetg⟩
  exact ⟨gSL, heq.symm⟩

end Submodule
