module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperOver
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBTwoCore
public import CFSG.LocalAnalysis.ComponentClassification.PrimeCore
public import CFSG.LocalAnalysis.ComponentInitial.KProperSubgroup

public section

namespace CFSG.ComponentClassification.CatalogueRelativeB

open CFSG.Assembly

@[expose] def InductionHypothesis (C : GroupProp) (G : Type) [Group G] : Prop :=
  ∀ (X : Type) [Group X] [Finite X], KProper C X →
    Nat.card X < Nat.card G → CentralTwoBInclusion.Property X

variable {C : GroupProp}

theorem proper_subgroup_B {G : Type} [Group G] [Finite G]
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hK : KProper C G) (ih : InductionHypothesis C G)
    (H : Subgroup G) (hproper : H ≠ ⊤) : CentralTwoBInclusion.Property H := by
  apply ih H (LocalAnalysis.ComponentInitial.kProper_subgroup hC hK H)
  simpa only [Subgroup.card_top] using Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hproper)

theorem smaller_quotient_B {G : Type} [Group G] [Finite G]
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hK : KProper C G) (ih : InductionHypothesis C G)
    (N : Subgroup G) [N.Normal] (hlt : Nat.card (G ⧸ N) < Nat.card G) :
    CentralTwoBInclusion.Property (G ⧸ N) :=
  ih (G ⧸ N) (CatalogueKProperOver.kProper_quotient hC hK N) hlt

theorem quotient_B_of_ne_bot {G : Type} [Group G] [Finite G]
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hK : KProper C G) (ih : InductionHypothesis C G)
    (N : Subgroup G) [N.Normal] (hne : N ≠ ⊥) : CentralTwoBInclusion.Property (G ⧸ N) :=
  smaller_quotient_B hC hK ih N (MinimalBCenter.quotient_card_lt N hne)

theorem odd_center_of_failure {G : Type} [Group G] [Finite G]
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hK : KProper C G) (ih : InductionHypothesis C G)
    (hfailure : ¬ CentralTwoBInclusion.Property G) : Odd (Nat.card (Subgroup.center G)) := by
  apply MinimalBCenter.odd_center _ hfailure
  intro N hnormal hlt
  let : N.Normal := hnormal
  exact smaller_quotient_B hC hK ih N hlt

theorem normal_two_eq_bot_of_failure {G : Type} [Group G] [Finite G]
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hK : KProper C G) (ih : InductionHypothesis C G)
    (hfailure : ¬ CentralTwoBInclusion.Property G)
    (N : Subgroup G) [N.Normal] (htwo : IsPGroup 2 N) : N = ⊥ :=
  MinimalBTwoCore.normal_two_eq_bot (odd_center_of_failure hC hK ih hfailure)
    (proper_subgroup_B hC hK ih) hfailure N htwo

theorem two_core_eq_bot_of_failure {G : Type} [Group G] [Finite G]
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hK : KProper C G) (ih : InductionHypothesis C G)
    (hfailure : ¬ CentralTwoBInclusion.Property G) : PrimeCore.subgroup 2 G = ⊥ := by
  let : (PrimeCore.subgroup 2 G).Normal := PrimeCore.normal 2 G
  exact normal_two_eq_bot_of_failure hC hK ih hfailure _ (PrimeCore.isPGroup 2 G)

theorem center_and_two_core_reduction {G : Type} [Group G] [Finite G]
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hK : KProper C G) (ih : InductionHypothesis C G)
    (S : Subgroup G) (hne : S ≠ ⊥) (htwo : IsPGroup 2 S)
    (hfailure : ¬ (TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G))).map
      (Subgroup.normalizer (S : Set G)).subtype ≤ TwoComponents.badSubgroup G) :
    Odd (Nat.card (Subgroup.center G)) ∧ PrimeCore.subgroup 2 G = ⊥ ∧
      (∀ z : G, orderOf z = 2 → z ∈ S →
        (∀ s ∈ S, z * s = s * z) →
        Subgroup.centralizer ({z} : Set G) ≠ ⊤ ∧
          ¬ (TwoComponents.badSubgroup (Subgroup.centralizer ({z} : Set G))).map
            (Subgroup.centralizer ({z} : Set G)).subtype ≤ TwoComponents.badSubgroup G) ∧
      ∃ z : G, orderOf z = 2 ∧ z ∈ S ∧ (∀ s ∈ S, z * s = s * z) ∧
        Subgroup.centralizer ({z} : Set G) ≠ ⊤ ∧
          ¬ (TwoComponents.badSubgroup (Subgroup.centralizer ({z} : Set G))).map
            (Subgroup.centralizer ({z} : Set G)).subtype ≤ TwoComponents.badSubgroup G := by
  have hglobalFailure : ¬ CentralTwoBInclusion.Property G :=
    fun hB => hfailure (hB S hne htwo)
  have hodd := odd_center_of_failure hC hK ih hglobalFailure
  have hcentralizer := BFailureLocalization.centralizer_failure hodd
    (proper_subgroup_B hC hK ih) S htwo hne hfailure
  obtain ⟨z, hz, hmem, hcentral⟩ := BFailureLocalization.exists_central_involution S htwo hne
  exact ⟨hodd, two_core_eq_bot_of_failure hC hK ih hglobalFailure, hcentralizer,
    z, hz, hmem, hcentral, hcentralizer z hz hmem hcentral⟩

end CFSG.ComponentClassification.CatalogueRelativeB
