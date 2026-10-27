module

public import CFSG.CharacterTheory.Wreathed.BaseAndDerived

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

universe u

variable {G : Type u} [Group G]

@[expose] def wreathModelHom {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    Wreath m →* G := (S : Subgroup G).subtype.comp e.symm.toMonoidHom

theorem wreathModelHom_injective {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    Function.Injective (wreathModelHom S e) :=
  (S : Subgroup G).subtype_injective.comp e.symm.injective

theorem wreathModelHom_range {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    (wreathModelHom S e).range = (S : Subgroup G) := by
  ext g
  constructor
  · rintro ⟨w, rfl⟩
    exact (e.symm w).property
  · intro hg
    exact ⟨e ⟨g, hg⟩, congrArg Subtype.val (e.symm_apply_apply ⟨g, hg⟩)⟩

@[expose] def modelBase {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) : Subgroup G :=
  (baseSubgroup m).map (wreathModelHom S e)

@[expose] def modelBaseEquiv {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    baseSubgroup m ≃* modelBase S e :=
  (baseSubgroup m).equivMapOfInjective (wreathModelHom S e)
    (wreathModelHom_injective S e)

theorem modelBase_le_sylow {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    modelBase S e ≤ (S : Subgroup G) := by
  rw [← wreathModelHom_range S e]
  exact Subgroup.map_le_range (f := wreathModelHom S e) (H := baseSubgroup m)

theorem sylow_le_modelBase_normalizer {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    (S : Subgroup G) ≤ Subgroup.normalizer (modelBase S e : Set G) := by
  have hnormal : (baseSubgroup m).Normal := by
    unfold baseSubgroup
    infer_instance
  let := hnormal
  have h := Subgroup.le_normalizer_map (H := baseSubgroup m) (wreathModelHom S e)
  rw [Subgroup.normalizer_eq_top, Subgroup.map_top, wreathModelHom_range S e] at h
  exact h

@[expose] def modelBaseNormalizerSylow {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    Sylow 2 (Subgroup.normalizer (modelBase S e : Set G)) :=
  S.subtype (sylow_le_modelBase_normalizer S e)

theorem modelBaseNormalizerSylow_coe {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    (modelBaseNormalizerSylow S e : Subgroup (Subgroup.normalizer (modelBase S e : Set G))) =
      (S : Subgroup G).subgroupOf (Subgroup.normalizer (modelBase S e : Set G)) :=
  Sylow.coe_subtype _ _

@[expose] def modelBaseAction {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    Subgroup.normalizer (modelBase S e : Set G) →* MulAut (baseSubgroup m) :=
  (MulAut.congr (modelBaseEquiv S e).symm).toMonoidHom.comp
    (modelBase S e).normalizerMonoidHom

theorem modelBaseAction_coe {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (g : Subgroup.normalizer (modelBase S e : Set G)) (b : baseSubgroup m) :
    wreathModelHom S e (modelBaseAction S e g b).val =
      g.val * wreathModelHom S e b.val * g.val⁻¹ := by
  change (((modelBaseEquiv S e) (modelBaseAction S e g b) : modelBase S e) : G) = _
  change (((modelBaseEquiv S e)
    ((modelBaseEquiv S e).symm ((modelBase S e).normalizerMonoidHom g
      ((modelBaseEquiv S e) b))) : modelBase S e) : G) = _
  rw [MulEquiv.apply_symm_apply]
  exact Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _

end CFSG.Wreathed
