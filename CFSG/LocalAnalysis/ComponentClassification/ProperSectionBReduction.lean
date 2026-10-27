module

public import CFSG.LocalAnalysis.ComponentClassification.ProperSectionBLayerSimple
public import CFSG.LocalAnalysis.ComponentClassification.BFailureCenterfreeTwoCore
public import CFSG.LocalAnalysis.ComponentClassification.BFailureOddKernel
public import CFSG.LocalAnalysis.ComponentClassification.LocalBFailureTwoLayer

public section

namespace CFSG.ComponentClassification.ProperSectionB

open Subgroup
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem smaller_quotient_B_of_ne_bot {G : Type*} [Group G]
    (hquot : ∀ (N : Subgroup G) (_ : N.Normal), N ≠ ⊥ → CentralTwoBInclusion.Property (G ⧸ N)) :
    ∀ (N : Subgroup G) (_ : N.Normal), Nat.card (G ⧸ N) < Nat.card G →
      CentralTwoBInclusion.Property (G ⧸ N) := by
  intro N hN hlt
  refine hquot N hN fun hbot => ?_
  change N.index < Nat.card G at hlt
  rw [hbot, Subgroup.index_bot] at hlt
  exact lt_irrefl _ hlt

theorem local_component_normalClosure_simple {C : CFSG.Assembly.GroupProp}
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X) (hS : SchreierFor C)
    {G : Type} [Group G] [Finite G] (hK : CFSG.Assembly.KProper C G)
    (hsub : ∀ X : Subgroup G, X ≠ ⊤ → CentralTwoBInclusion.Property X)
    (hfree : ∀ R : Subgroup G, R.Normal → Group.IsSolvable R → R = ⊥) {z : G}
    (hz : orderOf z = 2) (L : Subgroup (centralizer ({z} : Set G)))
    (hL : CFSG.IsPComponent 2 L) (hLq : ¬ CFSG.IsQuasisimple L)
    (hLB : ¬ L.map (centralizer ({z} : Set G)).subtype ≤ TwoComponents.badSubgroup G)
    {D : Subgroup G} (hD : D = normalClosure (L.map (centralizer ({z} : Set G)).subtype : Set G)) :
    D = commutator G ∧ D = CFSG.layer G ∧ D = CFSG.generalizedFitting G ∧ IsSimpleGroup D ∧
      (∃ a b : D, a * b ≠ b * a) ∧ D ⊔ zpowers z = ⊤ ∧ D.index ≤ 2 := by
  have hnorm : normalizer (zpowers z : Set G) = centralizer ({z} : Set G) :=
    LocalB.normalizer_zpowers_of_involution z hz
  have htwoZ : IsPGroup 2 (zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  have hneZ : zpowers z ≠ ⊥ := by
    intro hbot
    have hone : z = 1 := Subgroup.zpowers_eq_bot.mp hbot
    rw [hone, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hKle : L.map (centralizer ({z} : Set G)).subtype ≤ normalizer (zpowers z : Set G) := by
    rw [hnorm]
    exact Subgroup.map_subtype_le _
  have hKtwo : TwoComponents.IsTwoComponent ((L.map (centralizer ({z} : Set G)).subtype).subgroupOf
      (normalizer (zpowers z : Set G))) := by
    rw [hnorm]
    change TwoComponents.IsTwoComponent ((L.map (centralizer ({z} : Set G)).subtype).comap
      (centralizer ({z} : Set G)).subtype)
    rw [Subgroup.comap_map_eq_self_of_injective (centralizer ({z} : Set G)).subtype_injective]
    exact (CatalogueBAlternating.pComponent_two_iff L).1 hL
  have hKq : ¬ CFSG.Open.IsQuasisimple (L.map (centralizer ({z} : Set G)).subtype) := fun hq =>
    hLq (CatalogueBAlternating.quasisimple_iff_native.2 (Components.quasisimple_of_equiv
      (L.equivMapOfInjective _ (centralizer ({z} : Set G)).subtype_injective) hq))
  have hcover := LocalBNormalGeneration.normalClosure_sup_two_eq_top hsub (zpowers z)
    (L.map (centralizer ({z} : Set G)).subtype) hneZ htwoZ hKle hKtwo hKq hLB
  rw [← hD] at hcover
  have hindex : D.index ≤ 2 := by
    have : D.Normal := by
      rw [hD]
      exact Subgroup.normalClosure_normal
    have h := LocalBNormalGeneration.index_le_card_of_normal_sup D (zpowers z) hcover
    rwa [Nat.card_zpowers, hz] at h
  obtain ⟨hDG, hDE, hsimple, hnab⟩ :=
    kProper_reduced_B_failure_ordinary_layer_derived_simplicity_of_schreier hC hS hK hfree hz L
      hL hLq hD hcover
  have hfitting : Fitting.subgroup G = ⊥ := hfree _ (Fitting.normal G) (Fitting.solvable G)
  have hF : D = CFSG.generalizedFitting G := by
    rw [CFSG.generalizedFitting_eq_componentClassification]
    change D = Fitting.subgroup G ⊔ Layer.subgroup G
    rw [hfitting, bot_sup_eq, ← CFSG.layer_eq_componentClassification, hDE]
  exact ⟨hDG, hDE, hF, hsimple, hnab, hcover, hindex⟩

theorem proper_section_B_failure_simple_unbalanced_reduction_of_schreier
    {C : CFSG.Assembly.GroupProp}
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X) (hS : SchreierFor C)
    {G : Type} [Group G] [Finite G] (hK : CFSG.Assembly.KProper C G)
    (hsub : ∀ X : Subgroup G, X ≠ ⊤ → CentralTwoBInclusion.Property X)
    (hquot : ∀ (N : Subgroup G) (_ : N.Normal), N ≠ ⊥ → CentralTwoBInclusion.Property (G ⧸ N))
    {S : Subgroup G} (hS1 : S ≠ ⊥) (hS2 : IsPGroup 2 S)
    (hfail : ¬ (TwoComponents.badSubgroup (normalizer (S : Set G))).map
      (normalizer (S : Set G)).subtype ≤ TwoComponents.badSubgroup G) :
    Odd (Nat.card (center G)) ∧ CFSG.pCore 2 G = ⊥ ∧
      (∀ R : Subgroup G, R.Normal → Group.IsSolvable R → R = ⊥) ∧
      (∃ z : G, orderOf z = 2 ∧ z ∈ S ∧ (∀ s ∈ S, z * s = s * z) ∧
        centralizer ({z} : Set G) ≠ ⊤ ∧
        ¬ (TwoComponents.badSubgroup (centralizer ({z} : Set G))).map
          (centralizer ({z} : Set G)).subtype ≤ TwoComponents.badSubgroup G) ∧
      ∀ z : G, orderOf z = 2 → z ∈ S → (∀ s ∈ S, z * s = s * z) →
        centralizer ({z} : Set G) ≠ ⊤ ∧
        ¬ (TwoComponents.badSubgroup (centralizer ({z} : Set G))).map
          (centralizer ({z} : Set G)).subtype ≤ TwoComponents.badSubgroup G ∧
        (∃ L : Subgroup (centralizer ({z} : Set G)), CFSG.IsPComponent 2 L ∧
          ¬ CFSG.IsQuasisimple L ∧
          ¬ L.map (centralizer ({z} : Set G)).subtype ≤ TwoComponents.badSubgroup G) ∧
        (∀ L : Subgroup (centralizer ({z} : Set G)), CFSG.IsPComponent 2 L →
          ¬ CFSG.IsQuasisimple L →
          ¬ L.map (centralizer ({z} : Set G)).subtype ≤ TwoComponents.badSubgroup G →
          ∀ D : Subgroup G,
            D = normalClosure (L.map (centralizer ({z} : Set G)).subtype : Set G) →
            D = commutator G ∧ D = CFSG.layer G ∧ D = CFSG.generalizedFitting G ∧
              IsSimpleGroup D ∧ (∃ a b : D, a * b ≠ b * a) ∧ D ⊔ zpowers z = ⊤ ∧
              D.index ≤ 2) ∧
        CFSG.oddCore (centralizer ({z} : Set G)) ≠ ⊥ := by
  have hfailure : ¬ CentralTwoBInclusion.Property G := fun hB => hfail (hB S hS1 hS2)
  have hsmaller := smaller_quotient_B_of_ne_bot hquot
  have hodd : Odd (Nat.card (center G)) := MinimalBCenter.odd_center hsmaller hfailure
  have htwo : CFSG.pCore 2 G = ⊥ :=
    BFailureCenterfree.centerfree_minimal_B_failure_two_core_trivial hodd hsub hS1 hS2 hfail
  have hfree : ∀ R : Subgroup G, R.Normal → Group.IsSolvable R → R = ⊥ := by
    have : Group.IsSolvable (CFSG.Open.componentClassificationOddCore G) :=
      CFSG.Milestones.odd_order_solvable (OddCore.odd_card G)
    exact MinimalBRadical.no_solvable_normal_of_proper_outer hsmaller hsub hfailure
      (CatalogueRelativeB.proper_quotient_component_outer hC hK hS)
  have hcent := BFailureLocalization.centralizer_failure hodd hsub S hS2 hS1 hfail
  refine ⟨hodd, htwo, hfree, ?_, fun z hz hzS hzc => ?_⟩
  · obtain ⟨z, hz, hzS, hzc⟩ := BFailureLocalization.exists_central_involution S hS2 hS1
    exact ⟨z, hz, hzS, hzc, hcent z hz hzS hzc⟩
  obtain ⟨hzne, hzfail⟩ := hcent z hz hzS hzc
  have hexists : ∃ L : Subgroup (centralizer ({z} : Set G)), CFSG.IsPComponent 2 L ∧
      ¬ CFSG.IsQuasisimple L ∧
      ¬ L.map (centralizer ({z} : Set G)).subtype ≤ TwoComponents.badSubgroup G := by
    have h := hzfail
    rw [LocalBFailure.badSubgroup_eq_badTwoComponentSubgroup (centralizer ({z} : Set G))] at h
    exact BFailureOdd.exists_pComponent_not_le_of_not_badTwo_le h
  refine ⟨hzne, hzfail, hexists, fun L hL hLq hLB D hD =>
    local_component_normalClosure_simple hC hS hK hsub hfree hz L hL hLq hLB hD, ?_⟩
  obtain ⟨L, hL, hLq, -⟩ := hexists
  intro hbot
  exact hLq (CatalogueBAlternating.quasisimple_iff_native.2
    (TwoComponents.ordinary_of_corefree hbot
      ((CatalogueBAlternating.pComponent_two_iff L).1 hL)).2.2)

end CFSG.ComponentClassification.ProperSectionB
