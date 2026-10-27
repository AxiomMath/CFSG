module

public import CFSG.LocalAnalysis.ComponentClassification.MinimalBSolvable
public import CFSG.LocalAnalysis.ComponentClassification.PerfectCyclicActions

public section

open CFSG.Open

namespace CFSG.ComponentClassification.MinimalBOddWitness

theorem exists_component {G : Type*} [Group G] [Finite G]
    (hsmaller : ∀ (subgroup : Subgroup G) (_ : subgroup.Normal),
      Nat.card (G ⧸ subgroup) < Nat.card G → CentralTwoBInclusion.Property (G ⧸ subgroup))
    (hproper : ∀ subgroup : Subgroup G, subgroup ≠ ⊤ → CentralTwoBInclusion.Property subgroup)
    (twoSubgroup : Subgroup G) (hne : twoSubgroup ≠ ⊥) (htwo : IsPGroup 2 twoSubgroup)
    (hfailure : ¬ (TwoComponents.badSubgroup (Subgroup.normalizer (twoSubgroup : Set G))).map
      (Subgroup.normalizer (twoSubgroup : Set G)).subtype ≤ TwoComponents.badSubgroup G)
    (solvableNormal : Subgroup G) [solvableNormal.Normal] [Group.IsSolvable solvableNormal]
    (hsolvableNe : solvableNormal ≠ ⊥) :
    ∃ (normalSubgroup : Subgroup G) (hnormal : normalSubgroup.Normal),
      letI : normalSubgroup.Normal := hnormal
      normalSubgroup ≤ solvableNormal ∧
      MinimalNormal.Property normalSubgroup ∧ normalSubgroup.Characteristic ∧
      Group.IsSolvable normalSubgroup ∧ Odd (Nat.card normalSubgroup) ∧
      ∃ component : Subgroup G,
        component ≤ Subgroup.normalizer (twoSubgroup : Set G) ∧
        TwoComponents.IsTwoComponent
          (component.subgroupOf (Subgroup.normalizer (twoSubgroup : Set G))) ∧
        Group.IsPerfect component ∧ ¬ IsQuasisimple component ∧
        ¬ component ≤ TwoComponents.badSubgroup G ∧
        component ≤ Subgroup.centralizer (twoSubgroup : Set G) ∧
        IsQuasisimple (component.map (QuotientGroup.mk' normalSubgroup)) ∧
        ¬ normalSubgroup.subgroupOf component ≤ Subgroup.center component := by
  have hglobalFailure : ¬ CentralTwoBInclusion.Property G :=
    fun hB => hfailure (hB twoSubgroup hne htwo)
  obtain ⟨normalSubgroup, hle, hminimal, hsolvable, hcharacteristic, _⟩ :=
    MinimalBSolvable.exists_characteristic_le hsmaller hproper hglobalFailure
      solvableNormal hsolvableNe
  let : Group.IsSolvable normalSubgroup := hsolvable
  let : normalSubgroup.Characteristic := hcharacteristic
  have hodd := MinimalBSolvable.odd_card hsmaller hproper hglobalFailure normalSubgroup hminimal
  let projection := QuotientGroup.mk' normalSubgroup
  have hkernel : projection.ker = normalSubgroup := QuotientGroup.ker_mk' normalSubgroup
  let : Group.IsSolvable projection.ker := by rw [hkernel]; infer_instance
  have hquotientB := hsmaller normalSubgroup inferInstance
    (MinimalBCenter.quotient_card_lt normalSubgroup hminimal.prop.2)
  obtain ⟨localComponent, hlocal, hlocalNotQuasisimple, hnotContained, himageQuasisimple,
    hnotCentral⟩ := OddKernelBObstruction.exists_bad_component projection
      (QuotientGroup.mk'_surjective _) (by rwa [hkernel]) hquotientB twoSubgroup hne htwo hfailure
  let normalizer := Subgroup.normalizer (twoSubgroup : Set G)
  let component := localComponent.map normalizer.subtype
  have hcomponentLe : component ≤ normalizer := Subgroup.map_subtype_le _
  have hcomponent : TwoComponents.IsTwoComponent (component.subgroupOf normalizer) := by
    change TwoComponents.IsTwoComponent ((localComponent.map normalizer.subtype).comap
      normalizer.subtype)
    rw [Subgroup.comap_map_eq_self_of_injective normalizer.subtype_injective]
    exact hlocal
  let : Group.IsPerfect localComponent := ⟨TwoComponents.perfect hlocal⟩
  let : Group.IsPerfect component := Group.IsPerfect.map normalizer.subtype
  have hnotQuasisimple : ¬ IsQuasisimple component := by
    intro hquasisimple
    exact hlocalNotQuasisimple (Components.quasisimple_of_equiv
      (localComponent.equivMapOfInjective normalizer.subtype normalizer.subtype_injective)
      hquasisimple)
  have hcentralizes := TwoComponentCentralizers.le_ambient_centralizer component twoSubgroup
    normalizer hcomponentLe Subgroup.le_normalizer le_rfl hcomponent htwo
  rw [hkernel] at hnotCentral
  exact ⟨normalSubgroup, inferInstance, hle, hminimal, hcharacteristic, hsolvable, hodd, component,
    hcomponentLe, hcomponent, inferInstance, hnotQuasisimple, hnotContained,
    hcentralizes, himageQuasisimple, hnotCentral⟩

theorem solvable_normal_le_derived_centralizer_eq_bot {G : Type*} [Group G] [Finite G]
    (hsmaller : ∀ (subgroup : Subgroup G) (_ : subgroup.Normal),
      Nat.card (G ⧸ subgroup) < Nat.card G → CentralTwoBInclusion.Property (G ⧸ subgroup))
    (hproper : ∀ subgroup : Subgroup G, subgroup ≠ ⊤ → CentralTwoBInclusion.Property subgroup)
    (hfailure : ¬ CentralTwoBInclusion.Property G)
    (solvableNormal : Subgroup G) [solvableNormal.Normal] [Group.IsSolvable solvableNormal]
    (hcentralizes : solvableNormal ≤ Subgroup.centralizer (commutator G : Set G)) :
    solvableNormal = ⊥ := by
  classical
  by_contra hne
  obtain ⟨twoSubgroup, htwoNe, htwo, hlocalFailure⟩ :
      ∃ twoSubgroup : Subgroup G, twoSubgroup ≠ ⊥ ∧ IsPGroup 2 twoSubgroup ∧
        ¬ (TwoComponents.badSubgroup (Subgroup.normalizer (twoSubgroup : Set G))).map
          (Subgroup.normalizer (twoSubgroup : Set G)).subtype ≤ TwoComponents.badSubgroup G := by
    by_contra hnone
    apply hfailure
    intro twoSubgroup htwoNe htwo
    by_contra hlocalFailure
    exact hnone ⟨twoSubgroup, htwoNe, htwo, hlocalFailure⟩
  obtain ⟨normalSubgroup, _, hnormalLe, _, _, _, _, component, _, _, hperfect,
    _, _, _, _, hnotCentral⟩ := exists_component hsmaller hproper twoSubgroup htwoNe htwo
      hlocalFailure solvableNormal hne
  let : Group.IsPerfect component := hperfect
  have hcomponentDerived : component ≤ commutator G := by
    calc
      component = ⁅component, component⁆ := Subgroup.commutator_eq_self.symm
      _ ≤ ⁅(⊤ : Subgroup G), ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = commutator G := rfl
  apply hnotCentral
  intro element hmem
  apply Subgroup.mem_center_iff.mpr
  intro other
  have hcommutes := Subgroup.mem_centralizer_iff.mp (hcentralizes (hnormalLe hmem))
    other.val (hcomponentDerived other.property)
  exact Subtype.ext hcommutes

theorem normal_cyclic_eq_bot {G : Type*} [Group G] [Finite G]
    (hsmaller : ∀ (subgroup : Subgroup G) (_ : subgroup.Normal),
      Nat.card (G ⧸ subgroup) < Nat.card G → CentralTwoBInclusion.Property (G ⧸ subgroup))
    (hproper : ∀ subgroup : Subgroup G, subgroup ≠ ⊤ → CentralTwoBInclusion.Property subgroup)
    (hfailure : ¬ CentralTwoBInclusion.Property G)
    (subgroup : Subgroup G) [subgroup.Normal] [IsCyclic subgroup] : subgroup = ⊥ := by
  let : Group.IsSolvable subgroup := Group.isSolvable_of_comm
    (isMulCommutative_iff.mp inferInstance)
  exact solvable_normal_le_derived_centralizer_eq_bot hsmaller hproper hfailure subgroup
    (PerfectCyclicActions.normal_cyclic_le_derived_centralizer subgroup)

theorem minimal_not_cyclic {G : Type*} [Group G] [Finite G]
    (hsmaller : ∀ (subgroup : Subgroup G) (_ : subgroup.Normal),
      Nat.card (G ⧸ subgroup) < Nat.card G → CentralTwoBInclusion.Property (G ⧸ subgroup))
    (hproper : ∀ subgroup : Subgroup G, subgroup ≠ ⊤ → CentralTwoBInclusion.Property subgroup)
    (hfailure : ¬ CentralTwoBInclusion.Property G)
    (subgroup : Subgroup G) (hminimal : MinimalNormal.Property subgroup) :
    ¬ IsCyclic subgroup := by
  intro hcyclic
  let : IsCyclic subgroup := hcyclic
  let : subgroup.Normal := hminimal.prop.1
  exact hminimal.prop.2 (normal_cyclic_eq_bot hsmaller hproper hfailure subgroup)

theorem elementaryAbelian_dimension_ge_two {G : Type*} [Group G] [Finite G]
    (subgroup : Subgroup G) (prime dimension : ℕ) (hprime : prime.Prime)
    (hcard : Nat.card subgroup = prime ^ dimension) (hnotCyclic : ¬ IsCyclic subgroup) :
    2 ≤ dimension := by
  by_contra hsmall
  have hcases : dimension = 0 ∨ dimension = 1 := by omega
  rcases hcases with rfl | rfl
  · have hbot : subgroup = ⊥ := Subgroup.card_eq_one.mp (by simpa using hcard)
    subst subgroup
    exact hnotCyclic inferInstance
  · let : Fact prime.Prime := ⟨hprime⟩
    exact hnotCyclic (isCyclic_of_prime_card (by simpa using hcard))

theorem fixed_subgroup_witness {G : Type*} [Group G] [Finite G]
    (hsmaller : ∀ (subgroup : Subgroup G) (_ : subgroup.Normal),
      Nat.card (G ⧸ subgroup) < Nat.card G → CentralTwoBInclusion.Property (G ⧸ subgroup))
    (hproper : ∀ subgroup : Subgroup G, subgroup ≠ ⊤ → CentralTwoBInclusion.Property subgroup)
    (twoSubgroup : Subgroup G) (hne : twoSubgroup ≠ ⊥) (htwo : IsPGroup 2 twoSubgroup)
    (hfailure : ¬ (TwoComponents.badSubgroup (Subgroup.normalizer (twoSubgroup : Set G))).map
      (Subgroup.normalizer (twoSubgroup : Set G)).subtype ≤ TwoComponents.badSubgroup G)
    (solvableNormal : Subgroup G) [solvableNormal.Normal] [Group.IsSolvable solvableNormal]
    (hsolvableNe : solvableNormal ≠ ⊥) :
    ∃ (normalSubgroup fixedSubgroup : Subgroup G) (prime dimension : ℕ),
      normalSubgroup ≤ solvableNormal ∧ MinimalNormal.Property normalSubgroup ∧
      normalSubgroup.Characteristic ∧ prime.Prime ∧ Odd prime ∧ 2 ≤ dimension ∧
      fixedSubgroup ≤ normalSubgroup ⊓ Subgroup.centralizer (twoSubgroup : Set G) ∧
      IsElemAbelian prime fixedSubgroup ∧ Nat.card fixedSubgroup = prime ^ dimension := by
  have hglobalFailure : ¬ CentralTwoBInclusion.Property G :=
    fun hB => hfailure (hB twoSubgroup hne htwo)
  obtain ⟨normalSubgroup, hnormal, hnormalLe, hminimal, hcharacteristic, hsolvable, _,
    component, _, _, hperfect, _, _, hcentralizes, _, hnotCentral⟩ :=
      exists_component hsmaller hproper twoSubgroup hne htwo hfailure solvableNormal hsolvableNe
  let : normalSubgroup.Normal := hnormal
  let : Group.IsSolvable normalSubgroup := hsolvable
  let : Group.IsPerfect component := hperfect
  obtain ⟨prime, _, hprime, hodd, _, helementary, _⟩ :=
    MinimalBSolvable.odd_elementaryAbelian hsmaller hproper hglobalFailure normalSubgroup hminimal
  let : Fact prime.Prime := ⟨hprime⟩
  let fixedSubgroup := normalSubgroup ⊓ component
  have hnotCyclic : ¬ IsCyclic (normalSubgroup.subgroupOf component) := by
    intro hcyclic
    let : IsCyclic (normalSubgroup.subgroupOf component) := hcyclic
    exact hnotCentral (PerfectCyclicActions.central_of_perfect (normalSubgroup.subgroupOf component))
  have hambientNotCyclic : ¬ IsCyclic fixedSubgroup := by
    intro hcyclic
    have hmap : (normalSubgroup.subgroupOf component).map component.subtype = fixedSubgroup :=
      Subgroup.subgroupOf_map_subtype normalSubgroup component
    let equivalence := (normalSubgroup.subgroupOf component).equivMapOfInjective
      component.subtype component.subtype_injective
    have himageCyclic : IsCyclic ((normalSubgroup.subgroupOf component).map component.subtype) :=
      hmap.symm ▸ hcyclic
    exact hnotCyclic (equivalence.isCyclic.mpr himageCyclic)
  have hfixedElementary : IsElemAbelian prime fixedSubgroup := by
    refine ⟨isMulCommutative_iff.mpr ?_, ?_⟩
    · intro left right
      have hcommutes := (isMulCommutative_iff.mp helementary.1)
        (⟨left.val, left.property.1⟩ : normalSubgroup)
        (⟨right.val, right.property.1⟩ : normalSubgroup)
      exact Subtype.ext (congrArg (fun element : normalSubgroup => (element : G)) hcommutes)
    · intro element hmem
      exact helementary.2 element hmem.1
  have hfixedPGroup : IsPGroup prime fixedSubgroup :=
    isPGroup_iff_pow_pow_eq_one.mpr fun element => ⟨1, by
      apply Subtype.ext
      simpa using hfixedElementary.2 element.val element.property⟩
  obtain ⟨dimension, hcard⟩ := hfixedPGroup.exists_card_eq
  have hdimension := elementaryAbelian_dimension_ge_two fixedSubgroup prime dimension
    hprime hcard hambientNotCyclic
  exact ⟨normalSubgroup, fixedSubgroup, prime, dimension, hnormalLe, hminimal, hcharacteristic,
    hprime, hodd, hdimension, le_inf inf_le_left (inf_le_right.trans hcentralizes),
    hfixedElementary, hcard⟩

end CFSG.ComponentClassification.MinimalBOddWitness
