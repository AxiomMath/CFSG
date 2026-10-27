module

public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.BFailureLocalization
public import CFSG.LocalAnalysis.ComponentClassification.LocalBNormalGeneration

public section

open CFSG.Open

namespace CFSG.ComponentClassification.MinimalBDerived

theorem involution_component_reduction {G : Type*} [Group G] [Finite G]
    (hsmaller : ∀ (subgroup : Subgroup G) (_ : subgroup.Normal),
      Nat.card (G ⧸ subgroup) < Nat.card G → CentralTwoBInclusion.Property (G ⧸ subgroup))
    (hproper : ∀ subgroup : Subgroup G, subgroup ≠ ⊤ → CentralTwoBInclusion.Property subgroup)
    (hfailure : ¬ CentralTwoBInclusion.Property G) :
    ∃ involution : G, orderOf involution = 2 ∧
      ∃ localComponent : Subgroup (Subgroup.centralizer ({involution} : Set G)),
        TwoComponents.IsTwoComponent localComponent ∧ ¬ IsQuasisimple localComponent ∧
        ¬ localComponent.map (Subgroup.centralizer ({involution} : Set G)).subtype ≤
          TwoComponents.badSubgroup G ∧
        Subgroup.normalClosure
          (localComponent.map (Subgroup.centralizer ({involution} : Set G)).subtype : Set G) =
            commutator G ∧ Group.IsPerfect (commutator G) ∧ commutator G ≠ ⊥ ∧
        (commutator G).index ≤ 2 ∧ commutator G ⊔ Subgroup.zpowers involution = ⊤ := by
  classical
  obtain ⟨involution, horder, _, hcentralizerFailure⟩ :=
    BFailureLocalization.exists_involution_centralizer_failure
      (MinimalBCenter.odd_center hsmaller hfailure) hproper hfailure
  let twoSubgroup := Subgroup.zpowers involution
  let normalizer := Subgroup.centralizer ({involution} : Set G)
  have hnormalizer : Subgroup.normalizer (twoSubgroup : Set G) = normalizer :=
    LocalB.normalizer_zpowers_of_involution involution horder
  have htwo : IsPGroup 2 twoSubgroup :=
    IsPGroup.of_card (n := 1) (by
      change Nat.card (Subgroup.zpowers involution) = 2 ^ 1
      simpa only [Nat.card_zpowers, pow_one] using horder)
  have hne : twoSubgroup ≠ ⊥ := by
    intro hbot
    have hone : involution = 1 := Subgroup.zpowers_eq_bot.mp hbot
    simp [hone] at horder
  have hlocalFailure : ¬ (TwoComponents.badSubgroup normalizer).map normalizer.subtype ≤
      TwoComponents.badSubgroup G := hcentralizerFailure
  obtain ⟨localComponent, hlocal, hlocalNotQuasisimple, hnotContained⟩ :
      ∃ localComponent : Subgroup normalizer, TwoComponents.IsTwoComponent localComponent ∧
        ¬ IsQuasisimple localComponent ∧
        ¬ localComponent.map normalizer.subtype ≤ TwoComponents.badSubgroup G := by
    by_contra hnone
    apply hlocalFailure
    apply Subgroup.map_le_iff_le_comap.mpr
    apply sSup_le
    intro localComponent hbad
    apply Subgroup.map_le_iff_le_comap.mp
    by_contra hnotContained
    exact hnone ⟨localComponent, hbad.1, hbad.2, hnotContained⟩
  let component := localComponent.map normalizer.subtype
  have hcomponentLe : component ≤ Subgroup.normalizer (twoSubgroup : Set G) := by
    rw [hnormalizer]
    exact Subgroup.map_subtype_le _
  have hcomponent : TwoComponents.IsTwoComponent
      (component.subgroupOf (Subgroup.normalizer (twoSubgroup : Set G))) := by
    rw [hnormalizer]
    change TwoComponents.IsTwoComponent ((localComponent.map normalizer.subtype).comap
      normalizer.subtype)
    rw [Subgroup.comap_map_eq_self_of_injective normalizer.subtype_injective]
    exact hlocal
  have hnotQuasisimple : ¬ IsQuasisimple component := fun hquasisimple =>
    hlocalNotQuasisimple (Components.quasisimple_of_equiv
      (localComponent.equivMapOfInjective normalizer.subtype normalizer.subtype_injective) hquasisimple)
  let : Group.IsPerfect localComponent := ⟨TwoComponents.perfect hlocal⟩
  let : Group.IsPerfect component := Group.IsPerfect.map normalizer.subtype
  have hderived := LocalBNormalGeneration.normalClosure_eq_derived_of_commutative hproper
    twoSubgroup component hne htwo inferInstance hcomponentLe hcomponent hnotQuasisimple hnotContained
  have hcover := LocalBNormalGeneration.normalClosure_sup_two_eq_top hproper twoSubgroup
    component hne htwo hcomponentLe hcomponent hnotQuasisimple hnotContained
  rw [hderived] at hcover
  have hperfect := LocalBNormalGeneration.perfect_normalClosure component
  rw [hderived] at hperfect
  have hderivedNe : commutator G ≠ ⊥ := by
    intro hbot
    apply hnotContained
    have hle : component ≤ Subgroup.normalClosure (component : Set G) := Subgroup.subset_normalClosure
    rw [hderived, hbot] at hle
    exact hle.trans bot_le
  have hindex := LocalBNormalGeneration.index_le_card_of_normal_sup (commutator G) twoSubgroup hcover
  change (commutator G).index ≤ Nat.card (Subgroup.zpowers involution) at hindex
  rw [Nat.card_zpowers, horder] at hindex
  exact ⟨involution, horder, localComponent, hlocal, hlocalNotQuasisimple, hnotContained,
    hderived, hperfect, hderivedNe, hindex, hcover⟩

theorem involution_reduction {G : Type*} [Group G] [Finite G]
    (hsmaller : ∀ (subgroup : Subgroup G) (_ : subgroup.Normal),
      Nat.card (G ⧸ subgroup) < Nat.card G → CentralTwoBInclusion.Property (G ⧸ subgroup))
    (hproper : ∀ subgroup : Subgroup G, subgroup ≠ ⊤ → CentralTwoBInclusion.Property subgroup)
    (hfailure : ¬ CentralTwoBInclusion.Property G) :
    ∃ involution : G, orderOf involution = 2 ∧
      Group.IsPerfect (commutator G) ∧ commutator G ≠ ⊥ ∧
      (commutator G).index ≤ 2 ∧ commutator G ⊔ Subgroup.zpowers involution = ⊤ ∧
      ¬ (TwoComponents.badSubgroup (Subgroup.centralizer ({involution} : Set G))).map
        (Subgroup.centralizer ({involution} : Set G)).subtype ≤ TwoComponents.badSubgroup G := by
  obtain ⟨involution, horder, localComponent, hlocal, hnotQuasi, hnotContained,
    _, hperfect, hderivedNe, hindex, hcover⟩ :=
    involution_component_reduction hsmaller hproper hfailure
  refine ⟨involution, horder, hperfect, hderivedNe, hindex, hcover, ?_⟩
  intro hbadContained
  have hbad : localComponent ≤ TwoComponents.badSubgroup
      (Subgroup.centralizer ({involution} : Set G)) := le_sSup ⟨hlocal, hnotQuasi⟩
  exact hnotContained ((Subgroup.map_mono hbad).trans hbadContained)

end CFSG.ComponentClassification.MinimalBDerived
