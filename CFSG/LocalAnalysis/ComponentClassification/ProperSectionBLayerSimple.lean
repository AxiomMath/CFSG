module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueRelativeBMinimal
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingPrime
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingSymmetric

public section

namespace CFSG.ComponentClassification.ProperSectionB

open Subgroup
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem normalClosure_eq_commutator_of_sup_zpowers {G : Type*} [Group G] (K : Subgroup G)
    [Group.IsPerfect K] (z : G) (hcover : normalClosure (K : Set G) ⊔ zpowers z = ⊤) :
    normalClosure (K : Set G) = commutator G := by
  have hperf : Group.IsPerfect (normalClosure (K : Set G)) :=
    LocalBNormalGeneration.perfect_normalClosure K
  have : (normalClosure (K : Set G)).Normal := Subgroup.normalClosure_normal
  refine le_antisymm ?_ (Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hcover
    inferInstance)
  calc normalClosure (K : Set G)
      = ⁅normalClosure (K : Set G), normalClosure (K : Set G)⁆ :=
        (Subgroup.isPerfect_iff.1 hperf).symm
    _ ≤ ⁅(⊤ : Subgroup G), ⊤⁆ := Subgroup.commutator_mono le_top le_top
    _ = commutator G := rfl

theorem kProper_reduced_B_failure_ordinary_layer_derived_simplicity_of_schreier
    {C : CFSG.Assembly.GroupProp}
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X) (hS : SchreierFor C)
    {G : Type} [Group G] [Finite G] (hK : CFSG.Assembly.KProper C G)
    (hfree : ∀ R : Subgroup G, R.Normal → Group.IsSolvable R → R = ⊥) {z : G}
    (hz : orderOf z = 2) (L : Subgroup (centralizer ({z} : Set G)))
    (hL : CFSG.IsPComponent 2 L) (hLq : ¬ CFSG.IsQuasisimple L) {D : Subgroup G}
    (hD : D = normalClosure (L.map (centralizer ({z} : Set G)).subtype : Set G))
    (hcover : D ⊔ zpowers z = ⊤) :
    D = commutator G ∧ D = CFSG.layer G ∧ IsSimpleGroup D ∧ ∃ a b : D, a * b ≠ b * a := by
  subst hD
  have hlocal : TwoComponents.IsTwoComponent L := (CatalogueBAlternating.pComponent_two_iff L).1 hL
  have hnq : ¬ CFSG.Open.IsQuasisimple L := fun h =>
    hLq (CatalogueBAlternating.quasisimple_iff_native.2 h)
  obtain ⟨hlayer, hsimple⟩ :=
    CatalogueRelativeB.layer_derived_simple hC hK hfree hS z hz L hlocal hnq hcover
  have : Group.IsPerfect L := CatalogueBAlternating.pComponent_perfect hL
  have : Group.IsPerfect (L.map (centralizer ({z} : Set G)).subtype) := Group.IsPerfect.map _
  have hDG := normalClosure_eq_commutator_of_sup_zpowers _ z hcover
  have hperf : Group.IsPerfect (commutator G) := by
    rw [← hDG]
    exact LocalBNormalGeneration.perfect_normalClosure _
  refine ⟨hDG, ?_, ?_, ?_⟩
  · rw [CFSG.layer_eq_componentClassification, hlayer, hDG]
  · rw [hDG]
    exact hsimple
  · rw [hDG]
    have hnoncomm := Group.IsPerfect.not_isMulCommutative (commutator G)
    simpa only [isMulCommutative_iff, not_forall] using hnoncomm

end CFSG.ComponentClassification.ProperSectionB
