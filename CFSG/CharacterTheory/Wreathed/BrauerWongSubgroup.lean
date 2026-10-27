module

public import CFSG.CharacterTheory.Wreathed.CentralizerFusion

public noncomputable section

namespace CFSG.Wreathed.BrauerWong

open CFSG.Wreathed

universe u

variable {G : Type u} [Group G] {n : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
  (X : Subgroup G) (hSX : (S : Subgroup G) ≤ X)

@[expose] def subSylow : Sylow 2 X := S.subtype hSX

@[expose] def subCoordinates : (subSylow S X hSX : Subgroup X) ≃* Wreath (2 ^ n) :=
  (Subgroup.subgroupOfEquivOfLe hSX).trans e

theorem subSylow_coe :
    (subSylow S X hSX : Subgroup X) = (S : Subgroup G).subgroupOf X :=
  Sylow.coe_subtype _ _

theorem subModelHom_comp :
    X.subtype.comp (wreathModelHom (subSylow S X hSX) (subCoordinates S e X hSX)) =
      wreathModelHom S e := rfl

theorem subModelHom_coe (w : Wreath (2 ^ n)) :
    (wreathModelHom (subSylow S X hSX) (subCoordinates S e X hSX) w : G) =
      wreathModelHom S e w := rfl

theorem sub_map_eq (P : Subgroup (Wreath (2 ^ n))) :
    P.map (wreathModelHom (subSylow S X hSX) (subCoordinates S e X hSX)) =
      (P.map (wreathModelHom S e)).subgroupOf X := by
  apply Subgroup.map_injective X.subtype_injective
  rw [Subgroup.map_map, subModelHom_comp, Subgroup.map_subgroupOf_eq_of_le]
  refine le_trans ?_ hSX
  rw [← wreathModelHom_range S e]
  exact Subgroup.map_le_range _ _

theorem subModelBase_eq :
    modelBase (subSylow S X hSX) (subCoordinates S e X hSX) = (modelBase S e).subgroupOf X :=
  sub_map_eq S e X hSX _

theorem subModelV_eq :
    modelV (subSylow S X hSX) (subCoordinates S e X hSX) = (modelV S e).subgroupOf X :=
  sub_map_eq S e X hSX _

theorem subModelCenter_eq :
    modelCenter (subSylow S X hSX) (subCoordinates S e X hSX) =
      (modelCenter S e).subgroupOf X :=
  sub_map_eq S e X hSX _

theorem subModelY_eq :
    modelY (subSylow S X hSX) (subCoordinates S e X hSX) = (modelY S e).subgroupOf X :=
  sub_map_eq S e X hSX _

theorem subVNormalizer_eq :
    Subgroup.normalizer (modelV (subSylow S X hSX) (subCoordinates S e X hSX) : Set X) =
      (Subgroup.normalizer (modelV S e : Set G)).subgroupOf X := by
  rw [subModelV_eq, Subgroup.subgroupOf_normalizer_eq ((modelV_le_sylow S e).trans hSX)]

variable (hN : Subgroup.normalizer (modelV S e : Set G) ≤ X)

@[expose] def subVNormalizerEquiv :
    Subgroup.normalizer (modelV (subSylow S X hSX) (subCoordinates S e X hSX) : Set X) ≃*
      Subgroup.normalizer (modelV S e : Set G) :=
  (MulEquiv.subgroupCongr (subVNormalizer_eq S e X hSX)).trans (Subgroup.subgroupOfEquivOfLe hN)

theorem subVNormalizerEquiv_coe
    (g : Subgroup.normalizer (modelV (subSylow S X hSX) (subCoordinates S e X hSX) : Set X)) :
    (subVNormalizerEquiv S e X hSX hN g).val = g.val.val := by
  unfold subVNormalizerEquiv
  rw [MulEquiv.trans_apply, Subgroup.subgroupOfEquivOfLe_apply_coe]
  exact congrArg Subtype.val (MulEquiv.subgroupCongr_apply _ g)

theorem subVAction_eq
    (g : Subgroup.normalizer (modelV (subSylow S X hSX) (subCoordinates S e X hSX) : Set X)) :
    modelVAction (subSylow S X hSX) (subCoordinates S e X hSX) g =
      modelVAction S e (subVNormalizerEquiv S e X hSX hN g) := by
  apply MulEquiv.ext
  intro v
  apply Subtype.ext
  apply wreathModelHom_injective S e
  have hleft := congrArg X.subtype
    (modelVAction_coe (subSylow S X hSX) (subCoordinates S e X hSX) g v)
  rw [map_mul, map_mul, map_inv] at hleft
  change wreathModelHom S e
      (modelVAction (subSylow S X hSX) (subCoordinates S e X hSX) g v).val =
    g.val.val * wreathModelHom S e v.val * g.val.val⁻¹ at hleft
  rw [modelVAction_coe, subVNormalizerEquiv_coe]
  exact hleft

theorem subVQuotientAction_eq :
    modelVQuotientAction (subSylow S X hSX) (subCoordinates S e X hSX) =
      (modelVQuotientAction S e).comp (subVNormalizerEquiv S e X hSX hN).toMonoidHom := by
  apply MonoidHom.ext
  intro g
  change CFSG.FiveTransitive.CharacteristicAutomorphism.quotient
      (Subgroup.center (Original.V (2 ^ n)))
      (modelVAction (subSylow S X hSX) (subCoordinates S e X hSX) g) = _
  rw [subVAction_eq]
  rfl

include hN in
theorem subVQuotientAction_range :
    (modelVQuotientAction (subSylow S X hSX) (subCoordinates S e X hSX)).range =
      (modelVQuotientAction S e).range := by
  rw [subVQuotientAction_eq S e X hSX hN, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (subVNormalizerEquiv S e X hSX hN).surjective, Subgroup.map_top]

include hN in
theorem subVSym3 [Finite G] (hn : 2 ≤ n)
    (hsix : Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸ modelVInnerCentralizer S e ≃*
      Equiv.Perm (Fin 3))) :
    Nonempty (Subgroup.normalizer
        (modelV (subSylow S X hSX) (subCoordinates S e X hSX) : Set X) ⧸
      modelVInnerCentralizer (subSylow S X hSX) (subCoordinates S e X hSX) ≃*
        Equiv.Perm (Fin 3)) := by
  obtain ⟨e3⟩ := hsix
  exact ⟨(modelVNormalizerQuotientEquiv n hn _ _).trans
    ((MulEquiv.subgroupCongr (subVQuotientAction_range S e X hSX hN)).trans
      ((modelVNormalizerQuotientEquiv n hn S e).symm.trans e3))⟩

end CFSG.Wreathed.BrauerWong
