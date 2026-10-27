module

public import CFSG.LargeExtraspecial.DWCaseIIHMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Module Submodule QuadraticMap CFSG.GroupTheory.GLnTwoSplitting
open LinearMap (BilinForm)

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] {q : QuadraticForm (ZMod 2) E}
  {U : Submodule (ZMod 2) E}

theorem q_add_eq_add_polar (q : QuadraticForm (ZMod 2) E) (x y : E) :
    q (x + y) = q x + q y + polar q x y := by
  rw [polar]
  ring

theorem polar_eq_zero_of_mem (hU : ∀ u ∈ U, q u = 0) {u v : E} (hu : u ∈ U) (hv : v ∈ U) :
    polar q u v = 0 := by
  rw [polar, hU _ (add_mem hu hv), hU u hu, hU v hv, sub_zero, sub_zero]

variable [FiniteDimensional (ZMod 2) E]

theorem exists_section (hq : q.polarBilin.Nondegenerate) (hU : ∀ u ∈ U, q u = 0)
    (hUU : LinearMap.BilinForm.orthogonal q.polarBilin U = U) {ω : BilinForm (ZMod 2) U}
    (hω : ω.Nondegenerate) :
    ∃ σ : U →ₗ[ZMod 2] E, (∀ x a : U, polar q (σ x) a = ω x a) ∧ ∀ x, q (σ x) = 0 := by
  set β : E →ₗ[ZMod 2] Module.Dual (ZMod 2) U := q.polarBilin.compl₂ U.subtype with hβ
  have hβapp : ∀ y (a : U), β y a = polar q y a := fun y a => rfl
  have hker : LinearMap.ker β = U := by
    ext y
    rw [LinearMap.mem_ker]
    constructor
    · intro h
      rw [← hUU, LinearMap.BilinForm.mem_orthogonal_iff]
      intro a ha
      have h1 := LinearMap.congr_fun h ⟨a, ha⟩
      rw [hβapp, LinearMap.zero_apply] at h1
      rw [polarBilin_apply_apply, polar_comm]
      exact h1
    · intro hy
      ext a
      rw [hβapp, LinearMap.zero_apply]
      exact polar_eq_zero_of_mem hU hy a.2
  have hsurj : Function.Surjective β := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    have h1 := LinearMap.finrank_range_add_finrank_ker β
    have h2 := LinearMap.BilinForm.finrank_orthogonal hq U
    rw [hUU] at h2
    rw [hker] at h1
    rw [Subspace.dual_finrank_eq]
    omega
  obtain ⟨j, hj⟩ := Module.projective_lifting_property β ω hsurj
  have hj' : ∀ x a : U, polar q (j x) a = ω x a := fun x a => by
    rw [← hβapp, ← LinearMap.comp_apply, hj]
  set B' := (q.comp j).toBilin (Module.finBasis (ZMod 2) U) with hB'def
  have hB' : ∀ x, B' x x = q (j x) := fun x => by
    have h1 := congrArg (fun Q : QuadraticForm (ZMod 2) U => Q x)
      (toQuadraticMap_toBilin (q.comp j) (Module.finBasis (ZMod 2) U))
    simpa [hB'def] using h1
  set φ : U →ₗ[ZMod 2] U := (ω.flip.toDual hω.flip).symm.toLinearMap ∘ₗ B'.flip with hφdef
  have hφ : ∀ x y, ω x (φ y) = B' x y := fun x y => by
    have h1 := LinearMap.BilinForm.toDual_def (B := ω.flip) hω.flip (m := φ y) (n := x)
    rw [hφdef, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
      LinearMap.flip_apply] at h1
    rw [h1]
    rfl
  refine ⟨j + U.subtype ∘ₗ φ, fun x a => ?_, fun x => ?_⟩
  · simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [polar_add_left, hj', polar_eq_zero_of_mem hU (φ x).2 a.2, add_zero]
  · simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [q_add_eq_add_polar, hU _ (φ x).2, hj', hφ, hB', add_zero]
    exact CharTwo.add_self_eq_zero _

theorem exists_invariant_section (hq : q.polarBilin.Nondegenerate) (hU : ∀ u ∈ U, q u = 0)
    (hUU : LinearMap.BilinForm.orthogonal q.polarBilin U = U) {ω : BilinForm (ZMod 2) U}
    (hωa : ω.IsAlt) (hω : ω.Nondegenerate) (h6 : 6 ≤ finrank (ZMod 2) U) {L : Type*} [Group L]
    (ρE : L →* (E ≃ₗ[ZMod 2] E)) (r : L →* (U ≃ₗ[ZMod 2] U)) (hρq : ∀ g x, q (ρE g x) = q x)
    (hr : ∀ g (u : U), ((r g u : U) : E) = ρE g u) (hrω : ∀ g x y, ω (r g x) (r g y) = ω x y)
    (hrt : ∀ v : U, ∃ g, ∀ x, r g x = x + ω x v • v) (hker : ∀ g, r g = 1 → ρE g = 1) :
    ∃ σ : U →ₗ[ZMod 2] E, (∀ x a : U, polar q (σ x) a = ω x a) ∧ (∀ x, q (σ x) = 0) ∧
      ∀ g x, ρE g (σ x) = σ (r g x) := by
  obtain ⟨σ, hσ1, hσ2⟩ := exists_section hq hU hUU hω
  have hρpolar : ∀ g x y, polar q (ρE g x) (ρE g y) = polar q x y := fun g x y => by
    rw [polar, polar, ← map_add, hρq, hρq, hρq]
  have hd : ∀ g (x : U), ρE g (σ ((r g).symm x)) - σ x ∈ U := by
    intro g x
    have hmem : ρE g (σ ((r g).symm x)) - σ x ∈
        LinearMap.BilinForm.orthogonal q.polarBilin U := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro a ha
      set x' := (r g).symm x with hx'
      set a' := (r g).symm ⟨a, ha⟩ with ha'
      have haa : a = ρE g a' := by
        rw [← hr, ha', LinearEquiv.apply_symm_apply]
      have e1 : polar q a (σ x) = ω x ⟨a, ha⟩ := by
        rw [polar_comm]
        exact hσ1 x ⟨a, ha⟩
      have e2 : polar q a (ρE g (σ x')) = ω x' a' := by
        rw [haa, hρpolar, polar_comm]
        exact hσ1 x' a'
      have e3 : ω x' a' = ω x ⟨a, ha⟩ := by
        have h1 := hrω g x' a'
        rw [hx', ha', LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
        exact h1.symm
      rw [polarBilin_apply_apply, polar_sub_right, e1, e2, e3, sub_self]
    rwa [hUU] at hmem
  let δ : L → Module.End (ZMod 2) U := fun g => LinearMap.codRestrict U
    ((ρE g).toLinearMap ∘ₗ σ ∘ₗ (r g).symm.toLinearMap - σ) (hd g)
  have hδapp : ∀ g x, ((δ g x : U) : E) = ρE g (σ ((r g).symm x)) - σ x := fun g x => rfl
  have hsymm : ∀ g h (x : U), (r (g * h)).symm x = (r h).symm ((r g).symm x) := by
    intro g h x
    rw [LinearEquiv.symm_apply_eq, map_mul, LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
  have H : IsSpCocycle ω r δ :=
    { isometry := hrω
      transvection := hrt
      alt := fun g x => by
        rw [← hσ1 x (δ g x), hδapp]
        have h1 : q (ρE g (σ ((r g).symm x))) = 0 := by rw [hρq, hσ2]
        have h2 := q_add_eq_add_polar q (σ x) (ρE g (σ ((r g).symm x)) - σ x)
        rw [add_sub_cancel, h1, hσ2, hU _ (hd g x), zero_add, zero_add] at h2
        exact h2.symm
      cocycle := fun g h => by
        ext x
        rw [LinearMap.add_apply, Submodule.coe_add, hδapp, conjE_apply, hr, hδapp, hδapp,
          hsymm, map_mul, LinearEquiv.mul_apply, map_sub]
        abel
      ker := fun g hg => by
        ext x
        rw [hδapp, hker g hg, hg]
        exact sub_self _ }
  obtain ⟨w, hw, hδw⟩ := H.exists_eq_conjE_add hωa hω h6
  refine ⟨σ + U.subtype ∘ₗ w, fun x a => ?_, fun x => ?_, fun g x => ?_⟩
  · simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [polar_add_left, hσ1, polar_eq_zero_of_mem hU (w x).2 a.2, add_zero]
  · simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [q_add_eq_add_polar, hσ2, hU _ (w x).2, hσ1, hw x, add_zero, add_zero]
  · have h1 := congrArg (fun X : Module.End (ZMod 2) U => ((X (r g x) : U) : E)) (hδw g)
    rw [hδapp, LinearEquiv.symm_apply_apply, LinearMap.add_apply, Submodule.coe_add,
      conjE_apply, LinearEquiv.symm_apply_apply, hr] at h1
    simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply, map_add]
    linear_combination (norm := abel_two) h1

end CFSG.LargeExtraspecial.DW
