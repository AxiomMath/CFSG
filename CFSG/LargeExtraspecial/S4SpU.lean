module

public import CFSG.LargeExtraspecial.OrthoF2SpRadical

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Module CFSG.LargeExtraspecial.OrthoF2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {β : LinearMap.BilinForm (ZMod 2) V}

@[expose] def spRhoLin (β : LinearMap.BilinForm (ZMod 2) V) (c d : V) (l : ZMod 2) :
    V →ₗ[ZMod 2] V where
  toFun x := x + β x c • d + (β x d + l * β x c) • c
  map_add' x y := by
    simp only [map_add, LinearMap.add_apply, add_smul, mul_add]
    abel
  map_smul' r x := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    module

theorem spRhoLin_apply (c d : V) (l : ZMod 2) (x : V) :
    spRhoLin β c d l x = x + β x c • d + (β x d + l * β x c) • c :=
  rfl

theorem spRhoLin_apply_c (hβ : β.IsAlt) {c d : V} (hcd : β c d = 0) (l : ZMod 2) (x : V) :
    β (spRhoLin β c d l x) c = β x c := by
  have hdc : β d c = 0 := by rw [isAlt_symm hβ, hcd]
  rw [spRhoLin_apply, map_add, map_add, map_smul, map_smul, LinearMap.add_apply,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, hdc, hβ.self_eq_zero,
    smul_zero, smul_zero, add_zero, add_zero]

theorem spRhoLin_apply_d (hβ : β.IsAlt) {c d : V} (hcd : β c d = 0) (l : ZMod 2) (x : V) :
    β (spRhoLin β c d l x) d = β x d := by
  rw [spRhoLin_apply, map_add, map_add, map_smul, map_smul, LinearMap.add_apply,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, hcd, hβ.self_eq_zero,
    smul_zero, smul_zero, add_zero, add_zero]

theorem add_add_add_add_self (x u w : V) : x + u + w + u + w = x := by
  calc x + u + w + u + w = x + (u + u) + (w + w) := by abel
    _ = x := by rw [vec_add_self, vec_add_self, add_zero, add_zero]

@[expose] noncomputable def spRho (hβ : β.IsAlt) {c d : V} (hcd : β c d = 0) (l : ZMod 2) :
    V ≃ₗ[ZMod 2] V :=
  LinearEquiv.ofInvolutive (spRhoLin β c d l) fun x => by
    rw [spRhoLin_apply c d l (spRhoLin β c d l x), spRhoLin_apply_c hβ hcd, spRhoLin_apply_d hβ hcd,
      spRhoLin_apply]
    exact add_add_add_add_self _ _ _

theorem spRho_apply (hβ : β.IsAlt) {c d : V} (hcd : β c d = 0) (l : ZMod 2) (x : V) :
    spRho hβ hcd l x = x + β x c • d + (β x d + l * β x c) • c :=
  rfl

theorem spRho_mem_isometryGroup (hβ : β.IsAlt) {c d : V} (hcd : β c d = 0) (l : ZMod 2) :
    spRho hβ hcd l ∈ TauCeti.BilinForm.isometryGroup β := by
  rw [TauCeti.BilinForm.mem_isometryGroup_iff]
  intro x y
  have hdc : β d c = 0 := by rw [isAlt_symm hβ, hcd]
  have hs : ∀ u w : V, β u w = β w u := isAlt_symm hβ
  simp only [spRho_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, hβ.self_eq_zero, hdc, hcd, mul_zero, add_zero]
  rw [hs d y, hs c y]
  ring_nf
  rw [show (2 : ZMod 2) = 0 from rfl]
  ring

theorem spRho_mem_spPointRadical (hβ : β.IsAlt) {c d : V} (hcd : β c d = 0) (l : ZMod 2) :
    spRho hβ hcd l ∈ spPointRadical β c := by
  have hdc : β d c = 0 := by rw [isAlt_symm hβ, hcd]
  refine ⟨spRho_mem_isometryGroup hβ hcd l, ?_, fun x hx => ?_, fun v => ?_⟩
  · rw [spRho_apply, hβ.self_eq_zero, hcd]
    simp
  · have hxc : β x c = 0 := by rw [isAlt_symm hβ, hx]
    rw [spRho_apply, hxc, zero_smul, add_zero, mul_zero, add_zero, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self c)
  · rw [spRho_apply, add_assoc, add_sub_cancel_left, map_add, map_smul, map_smul, hcd,
      hβ.self_eq_zero, smul_zero, smul_zero, add_zero]

theorem spRho_zero_one (hβ : β.IsAlt) (c : V) (h : β c 0 = 0) :
    spRho hβ h 1 = spTransvection β hβ c := by
  ext x
  rw [spRho_apply, spTransvection_apply, map_zero, smul_zero, add_zero, zero_add, one_mul]

theorem spRho_mul (hβ : β.IsAlt) {c d d' : V} (hcd : β c d = 0) (hcd' : β c d' = 0)
    (l l' : ZMod 2) (h : β c (d + d') = 0) :
    spRho hβ hcd l * spRho hβ hcd' l' = spRho hβ h (l + l' + β d d') := by
  have hdc' : β d' c = 0 := by rw [isAlt_symm hβ, hcd']
  ext x
  rw [LinearEquiv.mul_apply]
  change spRhoLin β c d l (spRhoLin β c d' l' x) = spRhoLin β c (d + d') _ x
  have e1 : β (spRhoLin β c d' l' x) c = β x c := spRhoLin_apply_c hβ hcd' l' x
  have e2 : β (spRhoLin β c d' l' x) d = β x d + β x c * β d' d := by
    rw [spRhoLin_apply, map_add, map_add, map_smul, map_smul, LinearMap.add_apply,
      LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, hcd, smul_zero, add_zero,
      smul_eq_mul]
  rw [spRhoLin_apply c d l (spRhoLin β c d' l' x), e1, e2, spRhoLin_apply, spRhoLin_apply,
    map_add, isAlt_symm hβ d' d]
  match_scalars <;> (ring_nf; try reduce_mod_char)

theorem spRho_add_self (hβ : β.IsAlt) {c d : V} (hcd : β c d = 0) (l : ZMod 2)
    (h : β c (d + c) = 0) : spRho hβ h l = spRho hβ hcd l := by
  ext x
  rw [spRho_apply, spRho_apply, map_add]
  match_scalars <;> (ring_nf; try reduce_mod_char)

theorem conj_spRho (hβ : β.IsAlt) {c d : V} (hcd : β c d = 0) (l : ZMod 2)
    {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ TauCeti.BilinForm.isometryGroup β)
    (h : β (g c) (g d) = 0) :
    g * spRho hβ hcd l * g⁻¹ = spRho hβ h l := by
  have hg' := TauCeti.BilinForm.mem_isometryGroup_iff.mp hg
  have e1 : ∀ x u, β (g⁻¹ x) u = β x (g u) := fun x u => by
    rw [← hg' (g⁻¹ x) u, show g (g⁻¹ x) = x from g.apply_symm_apply x]
  ext x
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, spRho_apply, spRho_apply, map_add, map_add,
    map_smul, map_smul, show g (g⁻¹ x) = x from g.apply_symm_apply x, e1, e1]

theorem conj_spTransvection (hβ : β.IsAlt) (c : V) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ TauCeti.BilinForm.isometryGroup β) :
    g * spTransvection β hβ c * g⁻¹ = spTransvection β hβ (g c) := by
  have hg' := TauCeti.BilinForm.mem_isometryGroup_iff.mp hg
  ext x
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, spTransvection_apply, spTransvection_apply,
    map_add, map_smul, show g (g⁻¹ x) = x from g.apply_symm_apply x]
  rw [← hg' (g⁻¹ x) c, show g (g⁻¹ x) = x from g.apply_symm_apply x]

theorem exists_eq_spRho [FiniteDimensional (ZMod 2) V] (hβ : β.IsAlt) (hnd : β.Nondegenerate)
    {c : V} (hc : c ≠ 0) {u : V ≃ₗ[ZMod 2] V} (hu : u ∈ spPointRadical β c) :
    ∃ (d : V) (hcd : β c d = 0) (l : ZMod 2), u = spRho hβ hcd l := by
  obtain ⟨b, hb⟩ : ∃ b, β c b ≠ 0 := by
    by_contra! h
    exact hc (hnd.1 c h)
  have hb1 : β c b = 1 := zmod2_eq_one_of_ne_zero hb
  have hbc : β b c = 1 := by rw [isAlt_symm hβ, hb1]
  set w := u b - b with hw
  have hcw : β c w = 0 := hu.2.2.2 b
  refine ⟨w, hcw, β b w, spPointRadical_ext hb1 hu (spRho_mem_spPointRadical hβ hcw _) ?_⟩
  rw [spRho_apply, hbc, one_smul, mul_one, zmod2_add_self, zero_smul, add_zero, hw]
  abel

theorem spTransvection_mem_U (hβ : β.IsAlt) (c : V) :
    spTransvection β hβ c ∈ spPointRadical β c :=
  spTransvection_mem_spPointRadical hβ c

theorem spRho_one_eq (hβ : β.IsAlt) {c d : V} (hcd : β c d = 0) :
    spRho hβ hcd 1 = spRho hβ hcd 0 * spTransvection β hβ c := by
  ext x
  simp only [LinearEquiv.mul_apply, spTransvection_apply, spRho_apply, map_add, map_smul,
    hβ.self_eq_zero, hcd]
  match_scalars <;> (ring_nf; try reduce_mod_char)

end CFSG.LargeExtraspecial.S4
