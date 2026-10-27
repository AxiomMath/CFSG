module

public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBDerived
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBRadical
public import CFSG.LocalAnalysis.ComponentClassification.ProperComponentInputs

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.ComponentClassification.OrderFormMinimalB

theorem radical_free {G : Type groupUniverse} [Group G] [Finite G]
    (hK : IsKProperByOrder G)
    (hsmaller : ∀ (subgroup : Subgroup G) (_ : subgroup.Normal),
      Nat.card (G ⧸ subgroup) < Nat.card G → CentralTwoBInclusion.Property (G ⧸ subgroup))
    (hproper : ∀ subgroup : Subgroup G, subgroup ≠ ⊤ → CentralTwoBInclusion.Property subgroup)
    (hfailure : ¬ CentralTwoBInclusion.Property G)
    (hodd : ∀ (sectionGroup : Type groupUniverse) [Group sectionGroup] [Finite sectionGroup],
      Odd (Nat.card sectionGroup) → Group.IsSolvable sectionGroup)
    (hschreier : ∀ (sectionGroup : Type groupUniverse) [Group sectionGroup] [Finite sectionGroup]
      [IsSimpleGroup sectionGroup], (∃ left right : sectionGroup, left * right ≠ right * left) →
        Nat.card sectionGroup ∈ knownSimpleOrders → Group.IsSolvable (OuterAutomorphisms.Outer sectionGroup)) :
    SolvableRadical.Free G := by
  let : Group.IsSolvable (componentClassificationOddCore G) :=
    hodd _ (OddCore.odd_card G)
  apply MinimalBRadical.no_solvable_normal_of_proper_outer hsmaller hproper hfailure
  intro component hcomponent hproperComponent
  let simple := component ⧸ Subgroup.center component
  let : IsSimpleGroup simple := hcomponent.2.2.2
  have hnonab := Helpers.quasisimple_central_quotient_nonabelian component hcomponent.2.2
  have horder : Nat.card simple ∈ knownSimpleOrders :=
    Helpers.simple_quotient_order_of_surjective (G ⧸ componentClassificationOddCore G)
      (KProper.quotient hK _) component hproperComponent simple hnonab
        (QuotientGroup.mk' (Subgroup.center component)) (QuotientGroup.mk'_surjective _)
  exact hschreier simple hnonab horder

theorem simple_unbalanced_section {G : Type groupUniverse} [Group G] [Finite G]
    (hK : IsKProperByOrder G)
    (hsmaller : ∀ (subgroup : Subgroup G) (_ : subgroup.Normal),
      Nat.card (G ⧸ subgroup) < Nat.card G → CentralTwoBInclusion.Property (G ⧸ subgroup))
    (hproper : ∀ subgroup : Subgroup G, subgroup ≠ ⊤ → CentralTwoBInclusion.Property subgroup)
    (hfailure : ¬ CentralTwoBInclusion.Property G)
    (hodd : ∀ (sectionGroup : Type groupUniverse) [Group sectionGroup] [Finite sectionGroup],
      Odd (Nat.card sectionGroup) → Group.IsSolvable sectionGroup)
    (hschreier : ∀ (sectionGroup : Type groupUniverse) [Group sectionGroup] [Finite sectionGroup]
      [IsSimpleGroup sectionGroup], (∃ left right : sectionGroup, left * right ≠ right * left) →
        Nat.card sectionGroup ∈ knownSimpleOrders → Group.IsSolvable (OuterAutomorphisms.Outer sectionGroup)) :
    IsSimpleGroup (commutator G) ∧ Group.IsPerfect (commutator G) ∧
      GeneralizedFitting.subgroup G = commutator G ∧ (commutator G).index ≤ 2 ∧
      ∃ element : G, orderOf element = 2 ∧ commutator G ⊔ Subgroup.zpowers element = ⊤ ∧
        ¬ (TwoComponents.badSubgroup (Subgroup.centralizer ({element} : Set G))).map
          (Subgroup.centralizer ({element} : Set G)).subtype ≤ TwoComponents.badSubgroup G ∧
        componentClassificationOddCore (Subgroup.centralizer ({element} : Set G)) ≠ ⊥ := by
  have hfree := radical_free hK hsmaller hproper hfailure hodd hschreier
  obtain ⟨element, horder, localComponent, hlocal, hnotQuasi, hnotContained,
    hclosure, hperfect, _, hindex, hcover⟩ :=
    MinimalBDerived.involution_component_reduction hsmaller hproper hfailure
  have hclosureCover : Subgroup.normalClosure
      (localComponent.map (Subgroup.centralizer ({element} : Set G)).subtype : Set G) ⊔
        Subgroup.zpowers element = ⊤ := by rwa [hclosure]
  obtain ⟨hlayer, hsimple⟩ := ProperComponentInputs.layer_derived_simple hK hfree
    (fun subgroup => hodd subgroup)
    (fun component hsimple hnonab horder => by
      let : IsSimpleGroup component := hsimple
      exact hschreier component hnonab horder)
    element horder localComponent hlocal hnotQuasi hclosureCover
  have hfitting : Fitting.subgroup G = ⊥ := hfree _ (Fitting.normal G) (Fitting.solvable G)
  have hgeneralized : GeneralizedFitting.subgroup G = commutator G := by
    change Fitting.subgroup G ⊔ Layer.subgroup G = commutator G
    rw [hfitting, bot_sup_eq, hlayer]
  have hbad : localComponent ≤ TwoComponents.badSubgroup (Subgroup.centralizer ({element} : Set G)) :=
    le_sSup ⟨hlocal, hnotQuasi⟩
  have hbadFailure : ¬ (TwoComponents.badSubgroup (Subgroup.centralizer ({element} : Set G))).map
      (Subgroup.centralizer ({element} : Set G)).subtype ≤ TwoComponents.badSubgroup G := by
    intro hcontained
    exact hnotContained ((Subgroup.map_mono hbad).trans hcontained)
  have hlocalCore : componentClassificationOddCore (Subgroup.centralizer ({element} : Set G)) ≠ ⊥ := by
    intro hbot
    exact hnotQuasi (TwoComponents.ordinary_of_corefree hbot hlocal).2.2
  exact ⟨hsimple, hperfect, hgeneralized, hindex, element, horder, hcover, hbadFailure, hlocalCore⟩

end CFSG.ComponentClassification.OrderFormMinimalB
