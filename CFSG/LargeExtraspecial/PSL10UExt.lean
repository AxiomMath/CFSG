module

public import CFSG.LargeExtraspecial.PSL10Fix

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.PSLPSU10

open Module

variable {F : Type*} [Field F] {W : Type*} [AddCommGroup W] [Module F W]
  {U P : Submodule F W}

@[expose] noncomputable def extEnd (hc : IsCompl U P) : Module.End F P →* Module.End F W where
  toFun g := (Submodule.prodEquivOfIsCompl U P hc : U × P →ₗ[F] W) ∘ₗ
    LinearMap.prodMap LinearMap.id g ∘ₗ ((Submodule.prodEquivOfIsCompl U P hc).symm : W →ₗ[F] U × P)
  map_one' := LinearMap.ext fun x => by
    change Submodule.prodEquivOfIsCompl U P hc (LinearMap.prodMap LinearMap.id 1
      ((Submodule.prodEquivOfIsCompl U P hc).symm x)) = x
    rw [LinearMap.prodMap_apply, LinearMap.id_apply, Module.End.one_apply, Prod.mk.eta,
      LinearEquiv.apply_symm_apply]
  map_mul' g h := LinearMap.ext fun x => by
    change Submodule.prodEquivOfIsCompl U P hc (LinearMap.prodMap LinearMap.id (g * h)
      ((Submodule.prodEquivOfIsCompl U P hc).symm x)) =
      Submodule.prodEquivOfIsCompl U P hc (LinearMap.prodMap LinearMap.id g
        ((Submodule.prodEquivOfIsCompl U P hc).symm (Submodule.prodEquivOfIsCompl U P hc
          (LinearMap.prodMap LinearMap.id h ((Submodule.prodEquivOfIsCompl U P hc).symm x)))))
    rw [LinearEquiv.symm_apply_apply]
    rfl

theorem extEnd_apply (hc : IsCompl U P) (g : Module.End F P) (a : U) (b : P) :
    extEnd hc g ((a : W) + b) = a + g b := by
  have h : (a : W) + b = Submodule.prodEquivOfIsCompl U P hc (a, b) := rfl
  rw [h]
  change Submodule.prodEquivOfIsCompl U P hc (LinearMap.prodMap LinearMap.id g
    ((Submodule.prodEquivOfIsCompl U P hc).symm (Submodule.prodEquivOfIsCompl U P hc (a, b)))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem extEnd_apply_left (hc : IsCompl U P) (g : Module.End F P) {u : W} (hu : u ∈ U) :
    extEnd hc g u = u := by
  have h := extEnd_apply hc g ⟨u, hu⟩ 0
  simpa using h

theorem extEnd_apply_right (hc : IsCompl U P) (g : Module.End F P) (p : P) :
    extEnd hc g p = g p := by
  have h := extEnd_apply hc g 0 p
  simpa using h

theorem det_extEnd [FiniteDimensional F W] (hc : IsCompl U P) (g : Module.End F P) :
    LinearMap.det (extEnd hc g) = LinearMap.det g := by
  change LinearMap.det ((Submodule.prodEquivOfIsCompl U P hc : U × P →ₗ[F] W) ∘ₗ
    LinearMap.prodMap LinearMap.id g ∘ₗ
      ((Submodule.prodEquivOfIsCompl U P hc).symm : W →ₗ[F] U × P)) = _
  rw [LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_id, one_mul]

@[expose] noncomputable def extGL (hc : IsCompl U P) :
    LinearMap.GeneralLinearGroup F P →* LinearMap.GeneralLinearGroup F W :=
  Units.map (extEnd hc)

theorem coe_extGL (hc : IsCompl U P) (g : LinearMap.GeneralLinearGroup F P) :
    ((extGL hc g : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) = extEnd hc (g : P →ₗ[F] P) :=
  rfl

theorem extGL_injective (hc : IsCompl U P) : Function.Injective (extGL hc) := by
  intro g g' h
  refine Units.ext (LinearMap.ext fun p => Subtype.ext ?_)
  have h1 := LinearMap.congr_fun (congrArg Units.val h) (p : W)
  rwa [coe_extGL, coe_extGL, extEnd_apply_right, extEnd_apply_right] at h1

theorem extEnd_isometry {σ : F →+* F} {B : W →ₛₗ[σ] W →ₗ[F] F} (hc : IsCompl U P)
    (hUP : ∀ u ∈ U, ∀ p ∈ P, B u p = 0) (hPU : ∀ p ∈ P, ∀ u ∈ U, B p u = 0)
    {g : Module.End F P} (hg : ∀ x y : P, B (g x : W) (g y : W) = B x y) (x y : W) :
    B (extEnd hc g x) (extEnd hc g y) = B x y := by
  obtain ⟨⟨a, b⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl U P hc).surjective x
  obtain ⟨⟨a', b'⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl U P hc).surjective y
  rw [Submodule.coe_prodEquivOfIsCompl', Submodule.coe_prodEquivOfIsCompl', extEnd_apply,
    extEnd_apply]
  simp only [map_add, LinearMap.add_apply]
  rw [hUP a a.2 _ (g b').2, hUP a a.2 _ b'.2, hPU _ (g b).2 a' a'.2, hPU _ b.2 a' a'.2, hg]

theorem exists_extGL_eq (hc : IsCompl U P) (g : LinearMap.GeneralLinearGroup F W)
    (hU : ∀ u ∈ U, (g : W →ₗ[F] W) u = u) (hP : ∀ p ∈ P, (g : W →ₗ[F] W) p ∈ P)
    (hP' : ∀ p ∈ P, ((g⁻¹ : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) p ∈ P) :
    ∃ g' : LinearMap.GeneralLinearGroup F P, extGL hc g' = g ∧
      ∀ p : P, ((g' : P →ₗ[F] P) p : W) = (g : W →ₗ[F] W) p := by
  have h1 : ∀ x, (g : W →ₗ[F] W) (((g⁻¹ : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) x) = x :=
    fun x => by rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply]
  have h2 : ∀ x, ((g⁻¹ : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) ((g : W →ₗ[F] W) x) = x :=
    fun x => by rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply]
  let g' : LinearMap.GeneralLinearGroup F P :=
    ⟨LinearMap.restrict (g : W →ₗ[F] W) hP,
      LinearMap.restrict ((g⁻¹ : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) hP',
      LinearMap.ext fun p => Subtype.ext (h1 p), LinearMap.ext fun p => Subtype.ext (h2 p)⟩
  refine ⟨g', Units.ext (LinearMap.ext fun x => ?_), fun p => rfl⟩
  obtain ⟨⟨a, b⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl U P hc).surjective x
  rw [coe_extGL, Submodule.coe_prodEquivOfIsCompl', extEnd_apply, map_add, hU a a.2]
  rfl

end CFSG.LargeExtraspecial.S14.PSLPSU10
