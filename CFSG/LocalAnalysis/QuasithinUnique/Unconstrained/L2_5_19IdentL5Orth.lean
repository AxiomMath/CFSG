module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentL5Inner
public import CFSG.LinearAlgebra.SteinbergBQWidthBound
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.QuasithinUnique.Id2519.Tab.L5

open Matrix Module

namespace Orth

abbrev V5 := Fin 5 → ZMod 2

local instance finiteDimensional_V5 : FiniteDimensional (ZMod 2) V5 := Module.Finite.pi

noncomputable abbrev formOf (c : M5) : LinearMap.BilinForm (ZMod 2) V5 := Matrix.toBilin' c

theorem formOf_apply (c : M5) (x y : V5) : formOf c x y = x ⬝ᵥ (c *ᵥ y) :=
  Matrix.toBilin'_apply' c x y

theorem formOf_symm {c : M5} (hsym : cᵀ = c) (x y : V5) : formOf c x y = formOf c y x := by
  rw [formOf_apply, formOf_apply]
  calc x ⬝ᵥ c *ᵥ y = (x ᵥ* c) ⬝ᵥ y := Matrix.dotProduct_mulVec _ _ _
    _ = y ⬝ᵥ (x ᵥ* c) := dotProduct_comm _ _
    _ = y ⬝ᵥ c *ᵥ x := by rw [← Matrix.mulVec_transpose, hsym]

theorem formOf_nondegenerate {c : M5} (hdet : c.det ≠ 0) : (formOf c).Nondegenerate :=
  LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' c hdet

theorem formOf_diag_add {c : M5} (hsym : cᵀ = c) (x y : V5) :
    formOf c (x + y) (x + y) = formOf c x x + formOf c y y := by
  simp only [map_add, LinearMap.add_apply]
  rw [formOf_symm hsym y x]
  have h := CharTwo.add_self_eq_zero (formOf c x y)
  linear_combination h

theorem exists_charVector {c : M5} (hsym : cᵀ = c) (hdet : c.det ≠ 0) :
    ∃ ℓ : V5, ∀ x, formOf c x x = formOf c x ℓ := by
  let φ : V5 →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun x => formOf c x x
      map_add' := fun x y => formOf_diag_add hsym x y
      map_smul' := fun a x => by
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        rcases zmod2_cases a with rfl | rfl <;> simp }
  obtain ⟨ℓ, hℓ⟩ := (LinearMap.BilinForm.toDual (formOf c) (formOf_nondegenerate hdet)).surjective φ
  refine ⟨ℓ, fun x => ?_⟩
  have h := congrArg (fun f : Module.Dual (ZMod 2) V5 => f x) hℓ
  simp only [LinearMap.BilinForm.toDual_def] at h
  rw [formOf_symm hsym x ℓ, h]
  rfl

theorem formOf_charVector_self {c : M5} (hsym : cᵀ = c) (hdet : c.det ≠ 0) {ℓ : V5}
    (hℓ : ∀ x, formOf c x x = formOf c x ℓ) : formOf c ℓ ℓ = 1 := by
  have h := CFSG.LinearAlgebra.SteinbergBQ.bilin_charVector_self_eq_finrank (formOf c)
    (formOf_nondegenerate hdet) (formOf_symm hsym) hℓ
  have hfr : ((Module.finrank (ZMod 2) V5 : ℕ) : ZMod 2) = 1 := by
    rw [Module.finrank_fin_fun]
    decide
  exact h.trans hfr

section Hyperplane

variable {c : M5} {ℓ : V5}

noncomputable abbrev charFun (c : M5) (ℓ : V5) : V5 →ₗ[ZMod 2] ZMod 2 := (formOf c).flip ℓ

theorem charFun_apply (c : M5) (ℓ x : V5) : charFun c ℓ x = formOf c x ℓ := rfl

noncomputable abbrev hyper (c : M5) (ℓ : V5) : Submodule (ZMod 2) V5 := LinearMap.ker (charFun c ℓ)

theorem mem_hyper {x : V5} : x ∈ hyper c ℓ ↔ formOf c x ℓ = 0 := LinearMap.mem_ker

theorem split_mem (hℓ1 : formOf c ℓ ℓ = 1) (v : V5) : v + (formOf c v ℓ) • ℓ ∈ hyper c ℓ := by
  rw [mem_hyper, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hℓ1,
    mul_one]
  exact CharTwo.add_self_eq_zero _

theorem split_eq (v : V5) : v = (v + (formOf c v ℓ) • ℓ) + (formOf c v ℓ) • ℓ := by
  have h : (formOf c v ℓ) • ℓ + (formOf c v ℓ) • ℓ = 0 := by
    rw [← add_smul, CharTwo.add_self_eq_zero, zero_smul]
  calc v = v + ((formOf c v ℓ) • ℓ + (formOf c v ℓ) • ℓ) := by rw [h, add_zero]
    _ = (v + (formOf c v ℓ) • ℓ) + (formOf c v ℓ) • ℓ := by rw [add_assoc]

theorem finrank_hyper (hℓ1 : formOf c ℓ ℓ = 1) : finrank (ZMod 2) (hyper c ℓ) = 4 := by
  have h := LinearMap.finrank_range_add_finrank_ker (charFun c ℓ)
  have hr : LinearMap.range (charFun c ℓ) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro a
    refine ⟨a • ℓ, ?_⟩
    rw [charFun_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hℓ1, mul_one]
  rw [hr, finrank_top, Module.finrank_self] at h
  have h5 : finrank (ZMod 2) V5 = 5 := Module.finrank_fin_fun (ZMod 2)
  have h' : 1 + finrank (ZMod 2) (hyper c ℓ) = 5 := h.trans h5
  omega

noncomputable abbrev formW (c : M5) (ℓ : V5) : LinearMap.BilinForm (ZMod 2) (hyper c ℓ) :=
  (formOf c).restrict (hyper c ℓ)

theorem formW_apply (w w' : hyper c ℓ) : formW c ℓ w w' = formOf c w w' := rfl

theorem formW_isAlt (hℓ : ∀ x, formOf c x x = formOf c x ℓ) : (formW c ℓ).IsAlt := by
  intro w
  rw [formW_apply, hℓ]
  exact mem_hyper.mp w.2

theorem hyper_disjoint (hsym : cᵀ = c) (hdet : c.det ≠ 0) (hℓ1 : formOf c ℓ ℓ = 1) :
    Disjoint (hyper c ℓ) ((formOf c).orthogonal (hyper c ℓ)) := by
  rw [Submodule.disjoint_def]
  intro x hxW hxo
  apply (formOf_nondegenerate hdet).2 x
  intro v
  have h1 : formOf c (v + (formOf c v ℓ) • ℓ) x = 0 :=
    LinearMap.BilinForm.mem_orthogonal_iff.mp hxo _ (split_mem hℓ1 v)
  have h2 : formOf c ℓ x = 0 := by
    rw [formOf_symm hsym]
    exact mem_hyper.mp hxW
  rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, h2, mul_zero,
    add_zero] at h1
  exact h1

theorem formW_nondegenerate (hsym : cᵀ = c) (hdet : c.det ≠ 0) (hℓ1 : formOf c ℓ ℓ = 1) :
    (formW c ℓ).Nondegenerate :=
  LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal (formOf c)
    (fun x y h => by rw [formOf_symm hsym y x]; exact h) (hyper_disjoint hsym hdet hℓ1)

end Hyperplane

section Action

variable {c : M5} {ℓ : V5}

noncomputable abbrev actEquiv (g : S) : V5 ≃ₗ[ZMod 2] V5 := Matrix.SpecialLinearGroup.toLin' g

theorem actEquiv_apply (g : S) (x : V5) : actEquiv g x = (g : M5) *ᵥ x := by
  rw [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply]

theorem actEquiv_symm_apply (g : S) (x : V5) : (actEquiv g).symm x = ((g⁻¹ : S) : M5) *ᵥ x := by
  rw [Matrix.SpecialLinearGroup.toLin'_symm_apply, Matrix.toLin'_apply]

theorem preserves_form {g : S} (hg : (g : M5)ᵀ * c * g = c) (x y : V5) :
    formOf c ((g : M5) *ᵥ x) ((g : M5) *ᵥ y) = formOf c x y := by
  have h := congrArg (fun B : LinearMap.BilinForm (ZMod 2) V5 => B x y)
    (Matrix.toBilin'_comp c (g : M5) (g : M5))
  simp only [LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply] at h
  rw [hg] at h
  exact h

theorem fixes_charVector (hdet : c.det ≠ 0) (hℓ : ∀ x, formOf c x x = formOf c x ℓ)
    {g : S} (hg : (g : M5)ᵀ * c * g = c) : (g : M5) *ᵥ ℓ = ℓ := by
  have key : ∀ z : V5, formOf c z ((g : M5) *ᵥ ℓ) = formOf c z ℓ := by
    intro z
    obtain ⟨x, hx⟩ : ∃ x, (g : M5) *ᵥ x = z :=
      ⟨((g⁻¹ : S) : M5) *ᵥ z, by rw [Matrix.mulVec_mulVec, coe_mul_inv_self, Matrix.one_mulVec]⟩
    subst hx
    calc formOf c ((g : M5) *ᵥ x) ((g : M5) *ᵥ ℓ) = formOf c x ℓ := preserves_form hg x ℓ
      _ = formOf c x x := (hℓ x).symm
      _ = formOf c ((g : M5) *ᵥ x) ((g : M5) *ᵥ x) := (preserves_form hg x x).symm
      _ = formOf c ((g : M5) *ᵥ x) ℓ := hℓ _
  have h0 : ((g : M5) *ᵥ ℓ) - ℓ = 0 := by
    apply (formOf_nondegenerate hdet).2
    intro z
    rw [map_sub, key z, sub_self]
  exact sub_eq_zero.mp h0

theorem mem_hyper_of_preserves {g : S} (hg : (g : M5)ᵀ * c * g = c) (hgℓ : (g : M5) *ᵥ ℓ = ℓ)
    {w : V5} (hw : w ∈ hyper c ℓ) : (g : M5) *ᵥ w ∈ hyper c ℓ := by
  rw [mem_hyper] at hw ⊢
  have h := preserves_form hg w ℓ
  rw [hgℓ] at h
  rw [h]
  exact hw

@[expose] noncomputable def restrictEquiv (e : V5 ≃ₗ[ZMod 2] V5) (W : Submodule (ZMod 2) V5)
    (h : ∀ w ∈ W, e w ∈ W) (h' : ∀ w ∈ W, e.symm w ∈ W) : W ≃ₗ[ZMod 2] W where
  toFun w := ⟨e w, h w w.2⟩
  invFun w := ⟨e.symm w, h' w w.2⟩
  map_add' x y := Subtype.ext (map_add e (x : V5) (y : V5))
  map_smul' a x := Subtype.ext (map_smul e a (x : V5))
  left_inv w := Subtype.ext (e.symm_apply_apply w)
  right_inv w := Subtype.ext (e.apply_symm_apply w)

@[expose] noncomputable def restrictHom (W : Submodule (ZMod 2) V5) (H : Subgroup S)
    (h : ∀ g ∈ H, ∀ w ∈ W, (g : M5) *ᵥ w ∈ W) : H →* (W ≃ₗ[ZMod 2] W) where
  toFun g := restrictEquiv (actEquiv g) W (fun w hw => by rw [actEquiv_apply]; exact h g g.2 w hw)
    (fun w hw => by rw [actEquiv_symm_apply]; exact h g⁻¹ (H.inv_mem g.2) w hw)
  map_one' := LinearEquiv.ext fun w => Subtype.ext (by
    show (actEquiv ((1 : H) : S)) (w : V5) = w
    rw [actEquiv_apply, Subgroup.coe_one, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec])
  map_mul' g₁ g₂ := LinearEquiv.ext fun w => Subtype.ext (by
    show (actEquiv ((g₁ * g₂ : H) : S)) (w : V5) =
      (actEquiv (g₁ : S)) ((actEquiv (g₂ : S)) (w : V5))
    rw [actEquiv_apply, actEquiv_apply, actEquiv_apply, Subgroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec])

theorem coe_restrictHom (W : Submodule (ZMod 2) V5) (H : Subgroup S)
    (h : ∀ g ∈ H, ∀ w ∈ W, (g : M5) *ᵥ w ∈ W) (g : H) (w : W) :
    ((restrictHom W H h g w : W) : V5) = (g : M5) *ᵥ (w : V5) := by
  show (actEquiv (g : S)) (w : V5) = _
  exact actEquiv_apply _ _

theorem eq_one_of_trivial_on_hyper (hℓ1 : formOf c ℓ ℓ = 1) {g : S} (hgℓ : (g : M5) *ᵥ ℓ = ℓ)
    (hW : ∀ w ∈ hyper c ℓ, (g : M5) *ᵥ w = w) : g = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one]
  apply M5_ext_mulVec
  intro v
  rw [Matrix.one_mulVec]
  conv_lhs => rw [split_eq (c := c) (ℓ := ℓ) v]
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, hW _ (split_mem hℓ1 v), hgℓ]
  exact (split_eq (c := c) (ℓ := ℓ) v).symm

end Action

theorem card_dvd_of_form {c : M5} (hsym : cᵀ = c) (hdet : c.det ≠ 0) (H : Subgroup S)
    (hH : ∀ g ∈ H, (g : M5)ᵀ * c * g = c) : Nat.card H ∣ 720 := by
  obtain ⟨ℓ, hℓ⟩ := exists_charVector hsym hdet
  have hℓ1 := formOf_charVector_self hsym hdet hℓ
  have hstab : ∀ g ∈ H, ∀ w ∈ hyper c ℓ, (g : M5) *ᵥ w ∈ hyper c ℓ := fun g hg w hw =>
    mem_hyper_of_preserves (hH g hg) (fixes_charVector hdet hℓ (hH g hg)) hw
  have hmem : ∀ g : H, restrictHom (hyper c ℓ) H hstab g ∈
      TauCeti.BilinForm.isometryGroup (formW c ℓ) := by
    intro g
    rw [TauCeti.BilinForm.mem_isometryGroup_iff]
    intro w w'
    show formOf c ((restrictHom (hyper c ℓ) H hstab g w : hyper c ℓ) : V5)
      ((restrictHom (hyper c ℓ) H hstab g w' : hyper c ℓ) : V5) = formOf c (w : V5) (w' : V5)
    rw [coe_restrictHom, coe_restrictHom]
    exact preserves_form (hH g g.2) _ _
  let Θ : H →* TauCeti.BilinForm.isometryGroup (formW c ℓ) :=
    (restrictHom (hyper c ℓ) H hstab).codRestrict _ hmem
  have hinj : Function.Injective Θ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have h1 : restrictHom (hyper c ℓ) H hstab g = 1 := congrArg Subtype.val hg
    have h2 : (g : S) = 1 := by
      apply eq_one_of_trivial_on_hyper hℓ1 (fixes_charVector hdet hℓ (hH g g.2))
      intro w hw
      have h3 := congrArg
        (fun e : hyper c ℓ ≃ₗ[ZMod 2] hyper c ℓ => ((e ⟨w, hw⟩ : hyper c ℓ) : V5)) h1
      simp only [coe_restrictHom] at h3
      exact h3
    exact Subtype.ext h2
  have hcard : Nat.card (TauCeti.BilinForm.isometryGroup (formW c ℓ)) = 720 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_isometryGroup (K := ZMod 2) 2
      (formW c ℓ) (formW_isAlt hℓ) (formW_nondegenerate hsym hdet hℓ1)
      (by rw [finrank_hyper hℓ1]), Nat.card_zmod]
    decide
  rw [← hcard]
  exact Subgroup.card_dvd_of_injective Θ hinj

end Orth

end CFSG.QuasithinUnique.Id2519.Tab.L5
