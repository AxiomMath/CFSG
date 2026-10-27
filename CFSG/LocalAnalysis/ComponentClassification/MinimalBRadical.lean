module

public import CFSG.LocalAnalysis.ComponentClassification.OddQuotientLocalRecognition
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBOddWitness

public section

open CFSG.Open

namespace CFSG.ComponentClassification.MinimalBRadical

theorem no_solvable_normal_of_proper_outer {G : Type*} [Group G] [Finite G]
    (hsmaller : ∀ (subgroup : Subgroup G) (_ : subgroup.Normal),
      Nat.card (G ⧸ subgroup) < Nat.card G → CentralTwoBInclusion.Property (G ⧸ subgroup))
    (hproper : ∀ subgroup : Subgroup G, subgroup ≠ ⊤ → CentralTwoBInclusion.Property subgroup)
    (hfailure : ¬ CentralTwoBInclusion.Property G)
    [Group.IsSolvable (componentClassificationOddCore G)]
    (houter : ∀ component : Subgroup (G ⧸ componentClassificationOddCore G),
      IsComponentOf component ⊤ → component ≠ ⊤ →
        Group.IsSolvable (OuterAutomorphisms.Outer (component ⧸ Subgroup.center component))) :
    SolvableRadical.Free G := by
  intro solvableNormal hnormal hsolvable
  let : solvableNormal.Normal := hnormal
  let : Group.IsSolvable solvableNormal := hsolvable
  by_contra hne
  have hoddCenter := MinimalBCenter.odd_center hsmaller hfailure
  obtain ⟨element, horder, _, hlocalFailure⟩ :=
    BFailureLocalization.exists_involution_centralizer_failure hoddCenter hproper hfailure
  let cyclic := Subgroup.zpowers element
  let centralizer := Subgroup.centralizer ({element} : Set G)
  have hcyclicTwo : IsPGroup 2 cyclic := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, horder]; rfl)
  have hcyclicNe : cyclic ≠ ⊥ := by
    apply Subgroup.zpowers_ne_bot.mpr
    intro hone
    rw [hone, orderOf_one] at horder
    omega
  have hnormalizer : Subgroup.normalizer (cyclic : Set G) = centralizer :=
    OddKernelInvolutions.normalizer_cyclic_eq_centralizer element horder
  have hcyclicFailure : ¬ (TwoComponents.badSubgroup (Subgroup.normalizer (cyclic : Set G))).map
      (Subgroup.normalizer (cyclic : Set G)).subtype ≤ TwoComponents.badSubgroup G := by
    rw [hnormalizer]
    exact hlocalFailure
  obtain ⟨oddNormal, hoddNormal, _, _, _, hsolvableOdd, hodd,
    component, hnormalizerLe, htwoComponent, _, hnotQuasisimple, hnotBad,
    hcentralizesCyclic, himageQuasisimple, _⟩ :=
    MinimalBOddWitness.exists_component hsmaller hproper cyclic hcyclicNe hcyclicTwo
      hcyclicFailure solvableNormal hne
  let : oddNormal.Normal := hoddNormal
  let : Group.IsSolvable oddNormal := hsolvableOdd
  have hcentralizes : component ≤ centralizer := by
    intro member hmember
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact (Subgroup.mem_centralizer_iff.mp (hcentralizesCyclic hmember) element
      (Subgroup.mem_zpowers element)).symm
  have hlocalTwo : TwoComponents.IsTwoComponent (component.subgroupOf centralizer) := by
    rw [← hnormalizer]
    exact htwoComponent
  let projection := QuotientGroup.mk' oddNormal
  have hprojectionOdd : Odd (Nat.card projection.ker) := by rw [QuotientGroup.ker_mk']; exact hodd
  have hlocal := OddKernelInvolutions.twoComponent_quasisimple_image projection
    (QuotientGroup.mk'_surjective _) hprojectionOdd element horder component hcentralizes
    hlocalTwo himageQuasisimple
  exact hnotQuasisimple (OddQuotientLocalRecognition.local_twoComponent_quasisimple_of_odd_image_of_proper_outer
    oddNormal hodd element horder component hcentralizes hlocalTwo hnotBad hlocal houter).2

theorem no_solvable_normal {G : Type*} [Group G] [Finite G]
    (hsmaller : ∀ (subgroup : Subgroup G) (_ : subgroup.Normal),
      Nat.card (G ⧸ subgroup) < Nat.card G → CentralTwoBInclusion.Property (G ⧸ subgroup))
    (hproper : ∀ subgroup : Subgroup G, subgroup ≠ ⊤ → CentralTwoBInclusion.Property subgroup)
    (hfailure : ¬ CentralTwoBInclusion.Property G)
    [Group.IsSolvable (componentClassificationOddCore G)]
    (houter : ∀ component : Subgroup (G ⧸ componentClassificationOddCore G),
      IsComponentOf component ⊤ →
        Group.IsSolvable (OuterAutomorphisms.Outer (component ⧸ Subgroup.center component))) :
    SolvableRadical.Free G :=
  no_solvable_normal_of_proper_outer hsmaller hproper hfailure
    (fun component hcomponent _ => houter component hcomponent)

end CFSG.ComponentClassification.MinimalBRadical
