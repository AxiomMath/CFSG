module

public import CFSG.LocalAnalysis.ComponentClassification.MinimalBDerived
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBRadical
public import CFSG.LocalAnalysis.ComponentClassification.ReducedSemisimpleSimplicity

public section

open CFSG.Open

namespace CFSG.ComponentClassification.MinimalBSemisimple

theorem derived_simple_of_free {G : Type*} [Group G] [Finite G]
    (hsmaller : ∀ (subgroup : Subgroup G) (_ : subgroup.Normal),
      Nat.card (G ⧸ subgroup) < Nat.card G → CentralTwoBInclusion.Property (G ⧸ subgroup))
    (hproper : ∀ subgroup : Subgroup G, subgroup ≠ ⊤ → CentralTwoBInclusion.Property subgroup)
    (hfailure : ¬ CentralTwoBInclusion.Property G)
    (hfree : SolvableRadical.Free G)
    (heven : ∀ component : Subgroup G, IsComponentOf component ⊤ → 2 ∣ Nat.card component)
    (houter : ∀ component : Subgroup G, IsComponentOf component ⊤ →
      Group.IsSolvable (OuterAutomorphisms.Outer (component ⧸ Subgroup.center component))) :
    ∃ element : G, orderOf element = 2 ∧ Layer.subgroup G = commutator G ∧
      IsSimpleGroup (commutator G) ∧ Group.IsPerfect (commutator G) ∧
      (commutator G).index ≤ 2 ∧ commutator G ⊔ Subgroup.zpowers element = ⊤ := by
  obtain ⟨element, horder, localComponent, hlocal, hnotQuasi, _, hclosure,
    hperfect, _, hindex, hcover⟩ := MinimalBDerived.involution_component_reduction hsmaller hproper hfailure
  have hclosureCover : Subgroup.normalClosure
      (localComponent.map (Subgroup.centralizer ({element} : Set G)).subtype : Set G) ⊔
        Subgroup.zpowers element = ⊤ := by rwa [hclosure]
  obtain ⟨hlayer, hsimple⟩ := ReducedSemisimpleSimplicity.layer_derived_simple hfree element horder
    heven houter localComponent hlocal hnotQuasi hclosureCover
  exact ⟨element, horder, hlayer, hsimple, hperfect, hindex, hcover⟩

theorem derived_simple {G : Type*} [Group G] [Finite G]
    (hsmaller : ∀ (subgroup : Subgroup G) (_ : subgroup.Normal),
      Nat.card (G ⧸ subgroup) < Nat.card G → CentralTwoBInclusion.Property (G ⧸ subgroup))
    (hproper : ∀ subgroup : Subgroup G, subgroup ≠ ⊤ → CentralTwoBInclusion.Property subgroup)
    (hfailure : ¬ CentralTwoBInclusion.Property G)
    [Group.IsSolvable (componentClassificationOddCore G)]
    (heven : ∀ component : Subgroup G, IsComponentOf component ⊤ → 2 ∣ Nat.card component)
    (houter : ∀ component : Subgroup (G ⧸ componentClassificationOddCore G),
      IsComponentOf component ⊤ →
        Group.IsSolvable (OuterAutomorphisms.Outer (component ⧸ Subgroup.center component))) :
    ∃ element : G, orderOf element = 2 ∧ Layer.subgroup G = commutator G ∧
      IsSimpleGroup (commutator G) ∧ Group.IsPerfect (commutator G) ∧
      (commutator G).index ≤ 2 ∧ commutator G ⊔ Subgroup.zpowers element = ⊤ := by
  have hfree := MinimalBRadical.no_solvable_normal hsmaller hproper hfailure houter
  have hcore : componentClassificationOddCore G = ⊥ :=
    hfree _ inferInstance inferInstance
  let projection := QuotientGroup.mk' (componentClassificationOddCore G)
  have hkernel : projection.ker = ⊥ := by rw [QuotientGroup.ker_mk', hcore]
  let groupEquivalence := MulEquiv.ofBijective projection
    ⟨(MonoidHom.ker_eq_bot_iff projection).mp hkernel, QuotientGroup.mk'_surjective _⟩
  have hambientOuter : ∀ component : Subgroup G, IsComponentOf component ⊤ →
      Group.IsSolvable (OuterAutomorphisms.Outer (component ⧸ Subgroup.center component)) := by
    intro component hcomponent
    let image := component.map groupEquivalence.toMonoidHom
    have himage : IsComponentOf image ⊤ :=
      (LocalComponents.equiv_iff groupEquivalence component).mpr hcomponent
    let : Group.IsSolvable (OuterAutomorphisms.Outer (image ⧸ Subgroup.center image)) :=
      houter image himage
    exact OuterAutomorphisms.solvable_centerQuotient_of_equiv
      (component.equivMapOfInjective groupEquivalence.toMonoidHom groupEquivalence.injective).symm
  exact derived_simple_of_free hsmaller hproper hfailure hfree heven hambientOuter

theorem derived_quasisimple {G : Type*} [Group G] [Finite G]
    (hsmaller : ∀ (subgroup : Subgroup G) (_ : subgroup.Normal),
      Nat.card (G ⧸ subgroup) < Nat.card G → CentralTwoBInclusion.Property (G ⧸ subgroup))
    (hproper : ∀ subgroup : Subgroup G, subgroup ≠ ⊤ → CentralTwoBInclusion.Property subgroup)
    (hfailure : ¬ CentralTwoBInclusion.Property G)
    [Group.IsSolvable (componentClassificationOddCore G)]
    (heven : ∀ component : Subgroup G, IsComponentOf component ⊤ → 2 ∣ Nat.card component)
    (houter : ∀ component : Subgroup (G ⧸ componentClassificationOddCore G),
      IsComponentOf component ⊤ →
        Group.IsSolvable (OuterAutomorphisms.Outer (component ⧸ Subgroup.center component))) :
    IsQuasisimple (commutator G) := by
  obtain ⟨_, _, _, hsimple, hperfect, _, _⟩ :=
    derived_simple hsmaller hproper hfailure heven houter
  let : IsSimpleGroup (commutator G) := hsimple
  let : Group.IsPerfect (commutator G) := hperfect
  exact Quasisimple.simple_of_perfect (commutator G)

theorem simple_unbalanced_section {G : Type*} [Group G] [Finite G]
    (hsmaller : ∀ (subgroup : Subgroup G) (_ : subgroup.Normal),
      Nat.card (G ⧸ subgroup) < Nat.card G → CentralTwoBInclusion.Property (G ⧸ subgroup))
    (hproper : ∀ subgroup : Subgroup G, subgroup ≠ ⊤ → CentralTwoBInclusion.Property subgroup)
    (hfailure : ¬ CentralTwoBInclusion.Property G)
    [Group.IsSolvable (componentClassificationOddCore G)]
    (heven : ∀ component : Subgroup G, IsComponentOf component ⊤ → 2 ∣ Nat.card component)
    (houter : ∀ component : Subgroup (G ⧸ componentClassificationOddCore G),
      IsComponentOf component ⊤ →
        Group.IsSolvable (OuterAutomorphisms.Outer (component ⧸ Subgroup.center component))) :
    IsSimpleGroup (commutator G) ∧ Group.IsPerfect (commutator G) ∧
      GeneralizedFitting.subgroup G = commutator G ∧ (commutator G).index ≤ 2 ∧
      ∃ element : G, orderOf element = 2 ∧ commutator G ⊔ Subgroup.zpowers element = ⊤ ∧
        ¬ (TwoComponents.badSubgroup (Subgroup.centralizer ({element} : Set G))).map
          (Subgroup.centralizer ({element} : Set G)).subtype ≤ TwoComponents.badSubgroup G ∧
        componentClassificationOddCore (Subgroup.centralizer ({element} : Set G)) ≠ ⊥ := by
  have hfree := MinimalBRadical.no_solvable_normal hsmaller hproper hfailure houter
  obtain ⟨_, _, hlayer, hsimple, hperfect, hindex, _⟩ :=
    derived_simple hsmaller hproper hfailure heven houter
  have hfitting : Fitting.subgroup G = ⊥ :=
    hfree _ (Fitting.normal G) (Fitting.solvable G)
  have hgeneralized : GeneralizedFitting.subgroup G = commutator G := by
    change Fitting.subgroup G ⊔ Layer.subgroup G = commutator G
    rw [hfitting, bot_sup_eq, hlayer]
  obtain ⟨element, horder, localComponent, hlocal, hnotQuasi, hnotContained,
    _, _, _, _, hcover⟩ := MinimalBDerived.involution_component_reduction hsmaller hproper hfailure
  have hbad : localComponent ≤ TwoComponents.badSubgroup
      (Subgroup.centralizer ({element} : Set G)) := le_sSup ⟨hlocal, hnotQuasi⟩
  have hbadFailure : ¬ (TwoComponents.badSubgroup (Subgroup.centralizer ({element} : Set G))).map
      (Subgroup.centralizer ({element} : Set G)).subtype ≤ TwoComponents.badSubgroup G := by
    intro hcontained
    exact hnotContained ((Subgroup.map_mono hbad).trans hcontained)
  have hlocalCore : componentClassificationOddCore (Subgroup.centralizer ({element} : Set G)) ≠ ⊥ := by
    intro hbot
    exact hnotQuasi (TwoComponents.ordinary_of_corefree hbot hlocal).2.2
  exact ⟨hsimple, hperfect, hgeneralized, hindex, element, horder, hcover, hbadFailure, hlocalCore⟩

end CFSG.ComponentClassification.MinimalBSemisimple
