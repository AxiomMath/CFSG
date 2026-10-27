module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueRelativeBMinimal
public import CFSG.SignalizerFunctorTheorem.Inheritance.Sections

public section

namespace CFSG.ComponentClassification.CatalogueRelativeB

open CFSG.Assembly
open CFSG.SignalizerFunctorTheorem (IsSectionOf)
open LocalAnalysis.ComponentInitial (SchreierFor)

variable {C : GroupProp}

@[expose] def InductionHypothesisSec (C : GroupProp) (G : Type) [Group G] : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSectionOf X G → KProper C X →
    Nat.card X < Nat.card G → CentralTwoBInclusion.Property X

theorem proper_subgroup_B_sec {G : Type} [Group G] [Finite G]
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hK : KProper C G) (ih : InductionHypothesisSec C G)
    (H : Subgroup G) (hproper : H ≠ ⊤) : CentralTwoBInclusion.Property H := by
  apply ih H (IsSectionOf.of_subgroup H) (LocalAnalysis.ComponentInitial.kProper_subgroup hC hK H)
  simpa only [Subgroup.card_top] using Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hproper)

theorem smaller_quotient_B_sec {G : Type} [Group G] [Finite G]
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hK : KProper C G) (ih : InductionHypothesisSec C G)
    (N : Subgroup G) [N.Normal] (hlt : Nat.card (G ⧸ N) < Nat.card G) :
    CentralTwoBInclusion.Property (G ⧸ N) :=
  ih (G ⧸ N) (IsSectionOf.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N))
    (CatalogueKProperOver.kProper_quotient hC hK N) hlt

theorem radical_free_sec {G : Type} [Group G] [Finite G]
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hK : KProper C G) (ih : InductionHypothesisSec C G)
    (hfailure : ¬ CentralTwoBInclusion.Property G) (hschreier : SchreierFor C) :
    SolvableRadical.Free G := by
  let : Group.IsSolvable (CFSG.Open.componentClassificationOddCore G) :=
    CFSG.Milestones.odd_order_solvable (OddCore.odd_card G)
  apply MinimalBRadical.no_solvable_normal_of_proper_outer _
    (proper_subgroup_B_sec hC hK ih) hfailure (proper_quotient_component_outer hC hK hschreier)
  intro N hnormal hlt
  let : N.Normal := hnormal
  exact smaller_quotient_B_sec hC hK ih N hlt

theorem simple_unbalanced_section_sec {G : Type} [Group G] [Finite G]
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hK : KProper C G) (ih : InductionHypothesisSec C G)
    (hfailure : ¬ CentralTwoBInclusion.Property G) (hschreier : SchreierFor C) :
    IsSimpleGroup (commutator G) ∧ Group.IsPerfect (commutator G) ∧
      GeneralizedFitting.subgroup G = commutator G ∧ (commutator G).index ≤ 2 ∧
      ∃ z : G, orderOf z = 2 ∧ commutator G ⊔ Subgroup.zpowers z = ⊤ ∧
        ¬ (TwoComponents.badSubgroup (Subgroup.centralizer ({z} : Set G))).map
          (Subgroup.centralizer ({z} : Set G)).subtype ≤ TwoComponents.badSubgroup G ∧
        CFSG.Open.componentClassificationOddCore (Subgroup.centralizer ({z} : Set G)) ≠ ⊥ := by
  have hfree := radical_free_sec hC hK ih hfailure hschreier
  have hsmaller : ∀ (N : Subgroup G) (_ : N.Normal),
      Nat.card (G ⧸ N) < Nat.card G → CentralTwoBInclusion.Property (G ⧸ N) := by
    intro N hnormal hlt
    let : N.Normal := hnormal
    exact smaller_quotient_B_sec hC hK ih N hlt
  obtain ⟨z, hz, localComponent, hlocal, hnotQuasi, hnotContained,
    hclosure, hperfect, _, hindex, hcover⟩ :=
    MinimalBDerived.involution_component_reduction hsmaller (proper_subgroup_B_sec hC hK ih)
      hfailure
  have hclosureCover : Subgroup.normalClosure
      (localComponent.map (Subgroup.centralizer ({z} : Set G)).subtype : Set G) ⊔
        Subgroup.zpowers z = ⊤ := by rwa [hclosure]
  obtain ⟨hlayer, hsimple⟩ :=
    layer_derived_simple hC hK hfree hschreier z hz localComponent hlocal hnotQuasi hclosureCover
  have hfitting : Fitting.subgroup G = ⊥ := hfree _ (Fitting.normal G) (Fitting.solvable G)
  have hgeneralized : GeneralizedFitting.subgroup G = commutator G := by
    change Fitting.subgroup G ⊔ Layer.subgroup G = commutator G
    rw [hfitting, bot_sup_eq, hlayer]
  have hbad : localComponent ≤ TwoComponents.badSubgroup (Subgroup.centralizer ({z} : Set G)) :=
    le_sSup ⟨hlocal, hnotQuasi⟩
  have hbadFailure : ¬ (TwoComponents.badSubgroup (Subgroup.centralizer ({z} : Set G))).map
      (Subgroup.centralizer ({z} : Set G)).subtype ≤ TwoComponents.badSubgroup G := by
    intro hcontained
    exact hnotContained ((Subgroup.map_mono hbad).trans hcontained)
  have hlocalCore :
      CFSG.Open.componentClassificationOddCore (Subgroup.centralizer ({z} : Set G)) ≠ ⊥ := by
    intro hbot
    exact hnotQuasi (TwoComponents.ordinary_of_corefree hbot hlocal).2.2
  exact ⟨hsimple, hperfect, hgeneralized, hindex, z, hz, hcover, hbadFailure, hlocalCore⟩

end CFSG.ComponentClassification.CatalogueRelativeB
