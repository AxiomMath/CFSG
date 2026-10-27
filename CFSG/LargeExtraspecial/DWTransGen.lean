module

public import CFSG.LargeExtraspecial.DWTransQ
public import CFSG.LargeExtraspecial.S3Qa

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.GroupTheory.GLnTwoSplitting
open scoped IsMulCommutative

section Generation

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

@[expose] def goodCentres (T : Subgroup (E ≃ₗ[ZMod 2] E)) : Submodule (ZMod 2) E where
  carrier := {d | ∀ f : Dual (ZMod 2) E, f d = 0 → ∃ t ∈ T, ∀ x, t x = x + f x • d}
  zero_mem' f _ := ⟨1, T.one_mem, fun x => by rw [smul_zero, add_zero]; rfl⟩
  add_mem' {v w} hv hw f hf := by
    by_cases hv0 : v = 0
    · subst hv0
      rw [zero_add] at hf ⊢
      exact hw f hf
    by_cases hvw : v = w
    · subst hvw
      exact ⟨1, T.one_mem, fun x => by rw [two_add_self, smul_zero, add_zero]; rfl⟩
    have hind : v ∉ (ZMod 2) ∙ w := by
      rw [mem_span_singleton_iff_two]
      rintro (h | h)
      · exact hv0 h
      · exact hvw h
    obtain ⟨g, hgw, hgv⟩ := exists_dual_eq_one_of_notMem hind
    obtain ⟨t₁, ht₁, ht₁x⟩ := hw g (hgw w (Submodule.mem_span_singleton_self w))
    have ht₁t₁ : ∀ x, t₁ (t₁ x) = x := fun x => by
      rw [ht₁x, ht₁x, map_add, map_smul, hgw w (Submodule.mem_span_singleton_self w), smul_zero,
        add_zero, add_assoc, ← add_smul, zmod_two_add_self, zero_smul, add_zero]
    have ht₁inv : ∀ x, (t₁⁻¹ : E ≃ₗ[ZMod 2] E) x = t₁ x := fun x => by
      change t₁.symm x = t₁ x
      rw [LinearEquiv.symm_apply_eq, ht₁t₁]
    have ht₁v : t₁ v = v + w := by rw [ht₁x, hgv, one_smul]
    obtain ⟨t₂, ht₂, ht₂x⟩ := hv (f ∘ₗ (t₁ : E →ₗ[ZMod 2] E))
      (by rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ht₁v, hf])
    refine ⟨t₁ * t₂ * t₁⁻¹, T.mul_mem (T.mul_mem ht₁ ht₂) (T.inv_mem ht₁), fun x => ?_⟩
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ht₁inv, ht₂x, map_add, map_smul, ht₁t₁,
      ht₁v, LinearMap.comp_apply, LinearEquiv.coe_coe, ht₁t₁]
  smul_mem' c v hv f hf := by
    rcases zmod_two_eq_zero_or_one c with rfl | rfl
    · exact ⟨1, T.one_mem, fun x => by rw [zero_smul, smul_zero, add_zero]; rfl⟩
    · rw [one_smul] at hf ⊢
      exact hv f hf

theorem eq_top_of_transvections [FiniteDimensional (ZMod 2) E] (T : Subgroup (E ≃ₗ[ZMod 2] E))
    (s : Set E) (hs : ∀ U : Submodule (ZMod 2) E, s ⊆ U → U = ⊤)
    (h : ∀ d ∈ s, ∀ f : Dual (ZMod 2) E, f d = 0 → ∃ t ∈ T, ∀ x, t x = x + f x • d) :
    T = ⊤ := by
  have htop := hs (goodCentres T) fun d hd => h d hd
  rw [eq_top_iff, ← closure_transvections_eq_top, closure_le]
  rintro e ⟨f, d, hfd, rfl⟩
  have hd : d ∈ goodCentres T := by rw [htop]; exact Submodule.mem_top
  obtain ⟨t, ht, htx⟩ := hd f hfd
  have he : LinearEquiv.transvection hfd = t :=
    LinearEquiv.ext fun x => by rw [transvection_apply, htx x]
  rw [SetLike.mem_coe, he]
  exact ht

end Generation

namespace MaxEA

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {A : Subgroup G}
  [IsElementaryAbelian 2 A]

omit [IsElementaryAbelian 2 A] in
theorem conjBy (hA : MaxEA S A) {g : G} (hg : A ≤ S.Qa g) : MaxEA (S.conjBy g) A :=
  ⟨hg, by rw [S.width_conjBy]; exact hA.card_eq⟩

theorem exists_conjLinear_transvection_of_le_Qa (hA : MaxEA S A) {g : G} (hg : A ≤ S.Qa g)
    {x : Additive (AN A)} (hx : elt x = g * S.z * g⁻¹) {f : Dual (ZMod 2) (Additive (AN A))}
    (hf : f x = 0) :
    ∃ t ∈ (conjLinear (AN A)).range, ∀ y, t y = y + f y • x := by
  have hT := hA.conjBy hg
  have hzx : hT.zVec = x := elt_injective (by rw [elt_vec, hx]; rfl)
  obtain ⟨q, hq, hconj⟩ := hT.exists_conjLinear_eq_transvection (f := f) (by rw [hzx]; exact hf)
  refine ⟨_, ⟨_, hconj⟩, fun y => ?_⟩
  rw [transvection_apply, hzx]

theorem conjLinear_surjective_of_conj (hA : MaxEA S A)
    (hi : A ≤ closure {d : G | d ∈ A ∧ ∃ g : G, g * S.z * g⁻¹ = d})
    (hii : ∀ g : G, g * S.z * g⁻¹ ∈ A → A ≤ S.Qa g) :
    Function.Surjective (conjLinear (AN A)) := by
  have : Finite (Additive (AN A)) := inferInstanceAs (Finite (AN A))
  have : FiniteDimensional (ZMod 2) (Additive (AN A)) := Module.Finite.of_finite
  rw [← MonoidHom.range_eq_top]
  refine eq_top_of_transvections _ {x | ∃ g : G, g * S.z * g⁻¹ = elt x} (fun U hU => ?_)
    fun x ⟨g, hg⟩ f hf => hA.exists_conjLinear_transvection_of_le_Qa
      (hii g (hg ▸ elt_mem x)) hg.symm hf
  let U' : Subgroup G :=
    { carrier := {a | ∃ ha : a ∈ A, vec ha ∈ U}
      one_mem' := ⟨A.one_mem, U.zero_mem⟩
      mul_mem' := fun ⟨ha, hU⟩ ⟨hb, hV⟩ => ⟨A.mul_mem ha hb, U.add_mem hU hV⟩
      inv_mem' := fun ⟨ha, hU⟩ => ⟨A.inv_mem ha, U.neg_mem hU⟩ }
  have hle : closure {d : G | d ∈ A ∧ ∃ g : G, g * S.z * g⁻¹ = d} ≤ U' := by
    rw [closure_le]
    rintro d ⟨hdA, g, hg⟩
    exact ⟨hdA, hU ⟨g, hg⟩⟩
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨ha, hxU⟩ := hle (hi (elt_mem x))
  have : vec ha = x := elt_injective rfl
  rwa [this] at hxU

end MaxEA

end CFSG.LargeExtraspecial.DW
