module

public import CFSG.GroupTheory.GLnTwoSplitting.CanonicalGroup
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public section

namespace CFSG.GroupTheory.GLnTwoSplitting

open Module Submodule
open CFSG.LocalAnalysis.ComponentInitial

namespace NatExt

variable {G : Type*} [Group G] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  (X : NatExt G E)

@[expose] def stab (e₀ : E) : Subgroup G where
  carrier := {g | X.π g e₀ = e₀}
  mul_mem' {g h} hg hh := by
    change X.π (g * h) e₀ = e₀
    rw [map_mul, LinearEquiv.mul_apply, hh, hg]
  one_mem' := by
    change X.π 1 e₀ = e₀
    rw [map_one]
    rfl
  inv_mem' {g} hg := by
    change X.π g⁻¹ e₀ = e₀
    rw [map_inv]
    exact (LinearEquiv.symm_apply_eq _).2 hg.symm

theorem mem_stab {e₀ : E} {g : G} : g ∈ X.stab e₀ ↔ X.π g e₀ = e₀ :=
  Iff.rfl

@[expose] def centre (e₀ : E) : Subgroup G where
  carrier := {g | X.π g e₀ = e₀ ∧ ∀ w, X.π g w + w ∈ (ZMod 2) ∙ e₀}
  mul_mem' {g h} hg hh := by
    refine ⟨by rw [map_mul, LinearEquiv.mul_apply, hh.1, hg.1], fun w => ?_⟩
    rw [map_mul, LinearEquiv.mul_apply]
    have h1 := hg.2 (X.π h w)
    have h2 := hh.2 w
    have : X.π g (X.π h w) + w = (X.π g (X.π h w) + X.π h w) + (X.π h w + w) := by
      calc X.π g (X.π h w) + w = X.π g (X.π h w) + w + (X.π h w + X.π h w) := by
            rw [two_add_self, add_zero]
        _ = _ := by abel
    rw [this]
    exact add_mem h1 h2
  one_mem' := ⟨by rw [map_one]; rfl, fun w => by rw [map_one]; exact two_add_self w ▸ zero_mem _⟩
  inv_mem' {g} hg := by
    refine ⟨by rw [map_inv]; exact (LinearEquiv.symm_apply_eq _).2 hg.1.symm, fun w => ?_⟩
    have h1 := hg.2 ((X.π g)⁻¹ w)
    have h2 : X.π g ((X.π g)⁻¹ w) = w := LinearEquiv.apply_symm_apply _ _
    rw [h2, add_comm] at h1
    rwa [map_inv]

variable {X}

theorem mem_centre {e₀ : E} {g : G} :
    g ∈ X.centre e₀ ↔ X.π g e₀ = e₀ ∧ ∀ w, X.π g w + w ∈ (ZMod 2) ∙ e₀ :=
  Iff.rfl

theorem centre_le_stab (e₀ : E) : X.centre e₀ ≤ X.stab e₀ := fun _ hg => hg.1

theorem V_le_centre (e₀ : E) : X.V ≤ X.centre e₀ := by
  rintro _ ⟨v, rfl⟩
  refine ⟨by rw [X.π_ι]; rfl, fun w => ?_⟩
  rw [X.π_ι]
  exact (two_add_self w).symm ▸ zero_mem _

@[expose] def coeff (π₀ : Dual (ZMod 2) E) (g : G) : Dual (ZMod 2) E :=
  π₀ ∘ₗ ((X.π g : E →ₗ[ZMod 2] E) + LinearMap.id)

theorem coeff_apply (π₀ : Dual (ZMod 2) E) (g : G) (w : E) :
    X.coeff π₀ g w = π₀ (X.π g w + w) :=
  rfl

theorem coeff_apply_e₀ {e₀ : E} (π₀ : Dual (ZMod 2) E) {g : G} (hg : g ∈ X.centre e₀) :
    X.coeff π₀ g e₀ = 0 := by
  rw [coeff_apply, hg.1, two_add_self, map_zero]

theorem π_eq_transvection_coeff {e₀ : E} {π₀ : Dual (ZMod 2) E} (hπ₀ : π₀ e₀ = 1) {g : G}
    (hg : g ∈ X.centre e₀) :
    X.π g = LinearEquiv.transvection (X.coeff_apply_e₀ π₀ hg) := by
  ext w
  rw [transvection_apply, coeff_apply]
  obtain ⟨c, hc⟩ := mem_span_singleton.1 (hg.2 w)
  rw [← hc, map_smul, hπ₀, smul_eq_mul, mul_one, hc, add_comm (X.π g w) w, ← add_assoc,
    two_add_self, zero_add]

theorem coeff_mul {e₀ : E} {π₀ : Dual (ZMod 2) E} (hπ₀ : π₀ e₀ = 1) {g h : G}
    (hg : g ∈ X.centre e₀) (hh : h ∈ X.centre e₀) :
    X.coeff π₀ (g * h) = X.coeff π₀ g + X.coeff π₀ h := by
  ext w
  rw [LinearMap.add_apply, coeff_apply, coeff_apply, coeff_apply, map_mul, LinearEquiv.mul_apply]
  have hhw : X.π h w = w + X.coeff π₀ h w • e₀ := by
    rw [π_eq_transvection_coeff hπ₀ hh]
    rfl
  rw [hhw, (X.π g).map_add, (X.π g).map_smul, hg.1, ← map_add π₀]
  congr 1
  calc X.π g w + X.coeff π₀ h w • e₀ + w
      = X.π g w + X.coeff π₀ h w • e₀ + w + (w + w) := by rw [two_add_self, add_zero]
    _ = _ := by abel

theorem canonicalGroup_le_centre {hE : 6 ≤ finrank (ZMod 2) E} [FiniteDimensional (ZMod 2) E]
    {e₀ : E} {he₀ : e₀ ≠ 0} : X.canonicalGroup hE he₀ ≤ X.centre e₀ := by
  intro g hg
  obtain ⟨ψ, hψ, hgψ⟩ := X.exists_π_eq_of_mem_canonicalGroup hg
  refine ⟨by rw [hgψ, transvection_apply, hψ, zero_smul, add_zero], fun w => ?_⟩
  rw [hgψ, transvection_apply, add_comm w, add_assoc, two_add_self, add_zero]
  exact smul_mem _ _ (mem_span_singleton_self _)

section Quotient

open scoped Pointwise

theorem π_mem_stabilizer {e₀ : E} {g : G} (hg : g ∈ X.stab e₀) :
    X.π g ∈ MulAction.stabilizer (E ≃ₗ[ZMod 2] E) ((ZMod 2) ∙ e₀) := by
  rw [Submodule.mem_stabilizer_submodule_iff_map_eq, Submodule.map_span, Set.image_singleton]
  congr 2

variable (X) in
@[expose] noncomputable def quotAction (e₀ : E) :
    X.stab e₀ →* ((E ⧸ (ZMod 2) ∙ e₀) ≃ₗ[ZMod 2] (E ⧸ (ZMod 2) ∙ e₀)) :=
  (LinearEquiv.reduce ((ZMod 2) ∙ e₀)).comp
    (MonoidHom.codRestrict (X.π.comp (X.stab e₀).subtype) _ fun g => π_mem_stabilizer g.2)

theorem quotAction_mk {e₀ : E} (g : X.stab e₀) (w : E) :
    X.quotAction e₀ g (Submodule.Quotient.mk w) = Submodule.Quotient.mk (X.π g w) :=
  rfl

theorem quotAction_eq_one_iff {e₀ : E} (g : X.stab e₀) :
    X.quotAction e₀ g = 1 ↔ (g : G) ∈ X.centre e₀ := by
  constructor
  · intro h
    refine ⟨g.2, fun w => ?_⟩
    have := congrArg (fun φ : (E ⧸ (ZMod 2) ∙ e₀) ≃ₗ[ZMod 2] (E ⧸ (ZMod 2) ∙ e₀) =>
      φ (Submodule.Quotient.mk w)) h
    simp only [quotAction_mk] at this
    rw [← two_sub]
    exact (Submodule.Quotient.eq _).1 this
  · intro h
    ext q
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [quotAction_mk]
    exact (Submodule.Quotient.eq _).2 (by rw [two_sub]; exact h.2 w)

theorem quotAction_surjective [FiniteDimensional (ZMod 2) E] (e₀ : E) :
    Function.Surjective (X.quotAction e₀) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_transvections_eq_top,
    Subgroup.closure_le]
  rintro τ ⟨f, d, hfd, rfl⟩
  obtain ⟨d', rfl⟩ := Submodule.Quotient.mk_surjective _ d
  let f' : Dual (ZMod 2) E := f ∘ₗ ((ZMod 2) ∙ e₀).mkQ
  have hf' : f' d' = 0 := hfd
  obtain ⟨g, hg⟩ := X.surjective (LinearEquiv.transvection hf')
  have hge₀ : g ∈ X.stab e₀ := by
    change X.π g e₀ = e₀
    rw [hg, transvection_apply]
    have : f' e₀ = 0 := by
      change f (Submodule.Quotient.mk e₀) = 0
      rw [(Submodule.Quotient.mk_eq_zero _).2 (mem_span_singleton_self e₀), map_zero]
    rw [this, zero_smul, add_zero]
  refine ⟨⟨g, hge₀⟩, ?_⟩
  ext q
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [quotAction_mk]
  change Submodule.Quotient.mk (X.π g w) = _
  rw [hg, transvection_apply, transvection_apply, Submodule.Quotient.mk_add,
    Submodule.Quotient.mk_smul]
  rfl

end Quotient

section Matrix

variable {Q : Type*} [AddCommGroup Q] [Module (ZMod 2) Q] {m : ℕ}

theorem zmod_two_isUnit_eq_one {a : ZMod 2} (h : IsUnit a) : a = 1 :=
  zmod_two_eq_one_of_ne_zero h.ne_zero

@[expose] noncomputable def toSL (b : Basis (Fin m) (ZMod 2) Q) :
    (Q ≃ₗ[ZMod 2] Q) →* Matrix.SpecialLinearGroup (Fin m) (ZMod 2) where
  toFun f := ⟨LinearMap.toMatrix b b f, by
    rw [LinearMap.det_toMatrix]
    exact zmod_two_isUnit_eq_one (LinearEquiv.isUnit_det' f)⟩
  map_one' := Subtype.ext (LinearMap.toMatrix_id b)
  map_mul' f g := Subtype.ext (by
    change LinearMap.toMatrix b b ((f : Q →ₗ[ZMod 2] Q) ∘ₗ (g : Q →ₗ[ZMod 2] Q)) = _
    rw [LinearMap.toMatrix_comp b b b]
    rfl)

theorem toSL_injective (b : Basis (Fin m) (ZMod 2) Q) : Function.Injective (toSL b) := by
  intro f g h
  have h1 : LinearMap.toMatrix b b f = LinearMap.toMatrix b b g := congrArg Subtype.val h
  exact LinearEquiv.toLinearMap_injective ((LinearMap.toMatrix b b).injective h1)

theorem toSL_surjective (b : Basis (Fin m) (ZMod 2) Q) : Function.Surjective (toSL b) := by
  intro M
  refine ⟨Matrix.toLinearEquiv b (M : Matrix (Fin m) (Fin m) (ZMod 2))
    (by rw [M.2]; exact isUnit_one), Subtype.ext ?_⟩
  exact LinearMap.toMatrix_toLin b b _

theorem proj_injective_zmod_two (m : ℕ) :
    Function.Injective (LinearFlag.proj m (ZMod 2)) := by
  rw [← MonoidHom.ker_eq_bot_iff, LinearFlag.ker_proj, eq_bot_iff]
  rintro A ⟨c, -, hA⟩
  have hc : (c : ZMod 2) = 1 := zmod_two_isUnit_eq_one c.isUnit
  refine (Subgroup.mem_bot).2 (Subtype.ext ?_)
  rw [hA, hc]
  rfl

end Matrix

section StabHom

variable [FiniteDimensional (ZMod 2) E] {m : ℕ}

variable (X) in
@[expose] noncomputable def stabHom (e₀ : E) (hm : finrank (ZMod 2) (E ⧸ (ZMod 2) ∙ e₀) = m) :
    X.stab e₀ →* LinearFlag.projectiveSL m (ZMod 2) :=
  (LinearFlag.proj m (ZMod 2)).comp
    ((toSL (Module.finBasisOfFinrankEq (ZMod 2) _ hm)).comp (X.quotAction e₀))

theorem stabHom_surjective {e₀ : E} (hm : finrank (ZMod 2) (E ⧸ (ZMod 2) ∙ e₀) = m) :
    Function.Surjective (X.stabHom e₀ hm) :=
  (LinearFlag.proj_surjective m (ZMod 2)).comp
    ((toSL_surjective _).comp (X.quotAction_surjective e₀))

theorem stabHom_eq_one_iff {e₀ : E} (hm : finrank (ZMod 2) (E ⧸ (ZMod 2) ∙ e₀) = m)
    (g : X.stab e₀) : X.stabHom e₀ hm g = 1 ↔ (g : G) ∈ X.centre e₀ := by
  rw [← quotAction_eq_one_iff]
  constructor
  · intro h
    refine toSL_injective (Module.finBasisOfFinrankEq (ZMod 2) _ hm) ?_
    rw [map_one]
    exact proj_injective_zmod_two m (h.trans (map_one _).symm)
  · intro h
    change LinearFlag.proj m (ZMod 2) (toSL _ (X.quotAction e₀ g)) = 1
    rw [h, map_one, map_one]

end StabHom

end NatExt

end CFSG.GroupTheory.GLnTwoSplitting
