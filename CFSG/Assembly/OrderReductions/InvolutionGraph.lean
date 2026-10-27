module

public import Mathlib
public import CFSG.Mathlib.GroupTheory.Basic
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.TensorProduct.Finite

public section

namespace CFSG.OrderReductions.InvolutionGraph

open scoped Pointwise

abbrev Involution (group : Type*) [Group group] := {element : group // orderOf element = 2}

@[expose] def commutingGraph (group : Type*) [Group group] : SimpleGraph (Involution group) where
  Adj first second := first ≠ second ∧ Commute first.val second.val
  symm := by
    constructor
    intro first second adjacent
    exact ⟨adjacent.1.symm, adjacent.2.symm⟩
  loopless := by
    constructor
    intro element adjacent
    exact adjacent.1 rfl

theorem reachable_of_commute {group : Type*} [Group group]
    (first second : Involution group) (commuting : Commute first.val second.val) :
    (commutingGraph group).Reachable first second := by
  classical
  by_cases equal : first = second
  · exact equal ▸ SimpleGraph.Reachable.rfl
  · exact SimpleGraph.Adj.reachable ⟨equal, commuting⟩

@[expose] def mapInvolution {source target : Type*} [Group source] [Group target]
    (homomorphism : source →* target) (injective : Function.Injective homomorphism)
    (involution : Involution source) : Involution target :=
  ⟨homomorphism involution.val, by
    rw [orderOf_injective homomorphism injective, involution.property]⟩

@[expose] def mapGraph {source target : Type*} [Group source] [Group target]
    (homomorphism : source →* target) (injective : Function.Injective homomorphism) :
    commutingGraph source →g commutingGraph target where
  toFun := mapInvolution homomorphism injective
  map_rel' := by
    intro first second adjacent
    refine ⟨?_, adjacent.2.map homomorphism⟩
    intro equal_images
    exact adjacent.1 (Subtype.ext (injective (congrArg Subtype.val equal_images)))

@[expose] def involutionEquiv {source target : Type*} [Group source] [Group target]
    (equivalence : source ≃* target) : Involution source ≃ Involution target :=
  equivalence.toEquiv.subtypeEquiv (fun element => by
    change orderOf element = 2 ↔ orderOf (equivalence.toMonoidHom element) = 2
    rw [orderOf_injective equivalence.toMonoidHom equivalence.injective])

@[expose] def involutionsInEquiv {group : Type*} [Group group] (subgroup : Subgroup group) :
    {involution : Involution group // involution.val ∈ subgroup} ≃ Involution subgroup where
  toFun involution := ⟨⟨involution.val.val, involution.property⟩, by
    rw [← Subgroup.orderOf_coe]; exact involution.val.property⟩
  invFun involution := ⟨mapInvolution subgroup.subtype Subtype.val_injective involution,
    involution.val.property⟩
  left_inv involution := rfl
  right_inv involution := rfl

theorem exists_central_involution (group : Type*) [Group group] [Finite group]
    [Nontrivial group] (two_group : IsPGroup 2 group) :
    ∃ element : group, orderOf element = 2 ∧ element ∈ Subgroup.center group := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  let _ : Nontrivial (Subgroup.center group) := two_group.center_nontrivial
  have center_two_group : IsPGroup 2 (Subgroup.center group) :=
    two_group.of_injective (Subgroup.center group).subtype Subtype.val_injective
  obtain ⟨exponent, positive, center_order⟩ :=
    center_two_group.nontrivial_iff_card.mp inferInstance
  have divides : 2 ∣ Nat.card (Subgroup.center group) := by
    rw [center_order]
    exact dvd_pow_self 2 (by omega : exponent ≠ 0)
  obtain ⟨element, element_order⟩ := exists_prime_orderOf_dvd_card' 2 divides
  refine ⟨element.val, ?_, element.property⟩
  rwa [Subgroup.orderOf_coe]

theorem two_group_reachable (group : Type*) [Group group] [Finite group]
    (two_group : IsPGroup 2 group) (first second : Involution group) :
    (commutingGraph group).Reachable first second := by
  have first_ne_one : first.val ≠ 1 := by
    intro equal_one
    have order_eq := first.property
    rw [equal_one, orderOf_one] at order_eq
    omega
  have : Nontrivial group := nontrivial_of_ne first.val 1 first_ne_one
  obtain ⟨central, central_order, central_mem⟩ := exists_central_involution group two_group
  let center_vertex : Involution group := ⟨central, central_order⟩
  have first_commutes : Commute first.val central :=
    Subgroup.mem_center_iff.mp central_mem first.val
  have second_commutes : Commute second.val central :=
    Subgroup.mem_center_iff.mp central_mem second.val
  exact (reachable_of_commute first center_vertex first_commutes).trans
    (reachable_of_commute second center_vertex second_commutes).symm

theorem two_subgroup_reachable {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (two_group : IsPGroup 2 subgroup)
    (first second : Involution group) (first_mem : first.val ∈ subgroup)
    (second_mem : second.val ∈ subgroup) :
    (commutingGraph group).Reachable first second := by
  let first_vertex : Involution subgroup :=
    ⟨⟨first.val, first_mem⟩, by rw [← Subgroup.orderOf_coe]; exact first.property⟩
  let second_vertex : Involution subgroup :=
    ⟨⟨second.val, second_mem⟩, by rw [← Subgroup.orderOf_coe]; exact second.property⟩
  exact (two_group_reachable subgroup two_group first_vertex second_vertex).map
    (mapGraph subgroup.subtype Subtype.val_injective)

instance involutionAction (group : Type*) [Group group] : MulAction group (Involution group) where
  smul conjugator involution :=
    mapInvolution (MulAut.conj conjugator).toMonoidHom (MulAut.conj conjugator).injective involution
  one_smul involution := by
    apply Subtype.ext
    change (MulAut.conj (1 : group)) involution.val = involution.val
    simp
  mul_smul first second involution := by
    apply Subtype.ext
    change (MulAut.conj (first * second)) involution.val =
      (MulAut.conj first) ((MulAut.conj second) involution.val)
    simp [MulAut.conj_apply, mul_assoc]

theorem involution_smul_val {group : Type*} [Group group]
    (conjugator : group) (involution : Involution group) :
    (conjugator • involution).val = conjugator * involution.val * conjugator⁻¹ := rfl

@[expose] def conjugationGraph (group : Type*) [Group group] (conjugator : group) :
    commutingGraph group →g commutingGraph group :=
  mapGraph (MulAut.conj conjugator).toMonoidHom (MulAut.conj conjugator).injective

abbrev Component (group : Type*) [Group group] := (commutingGraph group).ConnectedComponent

instance componentAction (group : Type*) [Group group] : MulAction group (Component group) where
  smul conjugator component := component.map (conjugationGraph group conjugator)
  one_smul component := by
    induction component using SimpleGraph.ConnectedComponent.ind with
    | h involution =>
        change SimpleGraph.ConnectedComponent.map (conjugationGraph group 1)
          ((commutingGraph group).connectedComponentMk involution) = _
        rw [SimpleGraph.ConnectedComponent.map_mk]
        change (commutingGraph group).connectedComponentMk ((1 : group) • involution) = _
        rw [one_smul]
  mul_smul first second component := by
    induction component using SimpleGraph.ConnectedComponent.ind with
    | h involution =>
        change SimpleGraph.ConnectedComponent.map (conjugationGraph group (first * second))
          ((commutingGraph group).connectedComponentMk involution) =
          SimpleGraph.ConnectedComponent.map (conjugationGraph group first)
            (SimpleGraph.ConnectedComponent.map (conjugationGraph group second)
              ((commutingGraph group).connectedComponentMk involution))
        rw [SimpleGraph.ConnectedComponent.map_mk, SimpleGraph.ConnectedComponent.map_mk,
          SimpleGraph.ConnectedComponent.map_mk]
        change (commutingGraph group).connectedComponentMk ((first * second) • involution) =
          (commutingGraph group).connectedComponentMk (first • second • involution)
        rw [mul_smul]

theorem componentMk_smul {group : Type*} [Group group]
    (conjugator : group) (involution : Involution group) :
    conjugator • (commutingGraph group).connectedComponentMk involution =
      (commutingGraph group).connectedComponentMk (conjugator • involution) :=
  SimpleGraph.ConnectedComponent.map_mk (conjugationGraph group conjugator) involution

@[expose] def componentStabilizer {group : Type*} [Group group] (component : Component group) :
    Subgroup group := MulAction.stabilizer group component

theorem centralizer_le_componentStabilizer {group : Type*} [Group group]
    (involution : Involution group) :
    Subgroup.centralizer ({involution.val} : Set group) ≤
      componentStabilizer ((commutingGraph group).connectedComponentMk involution) := by
  intro conjugator centralizes
  change conjugator • (commutingGraph group).connectedComponentMk involution = _
  rw [componentMk_smul]
  have commuting : involution.val * conjugator = conjugator * involution.val :=
    Subgroup.mem_centralizer_iff.mp centralizes involution.val (by simp)
  have fixed : conjugator • involution = involution := by
    apply Subtype.ext
    rw [involution_smul_val, ← commuting, mul_assoc, mul_inv_cancel, mul_one]
  rw [fixed]

theorem involution_mem_componentStabilizer {group : Type*} [Group group]
    (involution : Involution group) :
    involution.val ∈
      componentStabilizer ((commutingGraph group).connectedComponentMk involution) := by
  apply centralizer_le_componentStabilizer involution
  rw [Subgroup.mem_centralizer_iff]
  intro element element_mem
  simpa only [Set.mem_singleton_iff] using element_mem ▸ (rfl :
    involution.val * involution.val = involution.val * involution.val)

theorem sylow_normalizer_le_componentStabilizer {group : Type*} [Group group] [Finite group]
    (sylow : Sylow 2 group) (involution : Involution group) (mem_sylow : involution.val ∈ sylow) :
    Subgroup.normalizer (sylow : Set group) ≤
      componentStabilizer ((commutingGraph group).connectedComponentMk involution) := by
  intro conjugator normalizes
  change conjugator • (commutingGraph group).connectedComponentMk involution = _
  rw [componentMk_smul]
  apply SimpleGraph.ConnectedComponent.sound
  apply two_subgroup_reachable (sylow : Subgroup group) sylow.isPGroup' _ _ _ mem_sylow
  rw [involution_smul_val]
  exact (Subgroup.mem_normalizer_iff.mp normalizes involution.val).mp mem_sylow

theorem exists_sylow_containing_involution {group : Type*} [Group group]
    (involution : Involution group) : ∃ sylow : Sylow 2 group, involution.val ∈ sylow := by
  have cyclic_two : IsPGroup 2 (Subgroup.zpowers involution.val) :=
    IsPGroup.of_card (p := 2) (n := 1)
      (by rw [Nat.card_zpowers, involution.property, pow_one])
  obtain ⟨sylow, contains⟩ := cyclic_two.exists_le_sylow
  exact ⟨sylow, contains (Subgroup.mem_zpowers involution.val)⟩

theorem componentStabilizer_contains_sylow {group : Type*} [Group group] [Finite group]
    (involution : Involution group) :
    ∃ sylow : Sylow 2 group,
      (sylow : Subgroup group) ≤
        componentStabilizer ((commutingGraph group).connectedComponentMk involution) := by
  obtain ⟨sylow, mem_sylow⟩ := exists_sylow_containing_involution involution
  refine ⟨sylow, ?_⟩
  exact (sylow : Subgroup group).le_normalizer.trans
    (sylow_normalizer_le_componentStabilizer sylow involution mem_sylow)

theorem involution_smul_mem_sylow {group : Type*} [Group group]
    (conjugator : group) (sylow : Sylow 2 group) (involution : Involution group)
    (mem_sylow : involution.val ∈ sylow) :
    (conjugator • involution).val ∈ conjugator • sylow := by
  change (conjugator • involution).val ∈ ((conjugator • sylow : Sylow 2 group) :
    Set group)
  rw [Sylow.coe_smul]
  exact ⟨involution.val, mem_sylow, rfl⟩

theorem components_transitive {group : Type*} [Group group] [Finite group]
    (first second : Component group) : ∃ conjugator : group, conjugator • first = second := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  induction first, second using SimpleGraph.ConnectedComponent.ind₂ with
  | h first second =>
      obtain ⟨first_sylow, first_mem⟩ := exists_sylow_containing_involution first
      obtain ⟨second_sylow, second_mem⟩ := exists_sylow_containing_involution second
      obtain ⟨conjugator, conjugates⟩ :=
        MulAction.exists_smul_eq group first_sylow second_sylow
      refine ⟨conjugator, ?_⟩
      rw [componentMk_smul]
      apply SimpleGraph.ConnectedComponent.sound
      apply two_subgroup_reachable (second_sylow : Subgroup group)
        second_sylow.isPGroup' _ _ _ second_mem
      rw [← conjugates]
      exact involution_smul_mem_sylow conjugator first_sylow first first_mem

theorem componentStabilizer_involution_iff {group : Type*} [Group group] [Finite group]
    (component : Component group) (involution : Involution group) :
    involution.val ∈ componentStabilizer component ↔
      (commutingGraph group).connectedComponentMk involution = component := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  induction component using SimpleGraph.ConnectedComponent.ind with
  | h first =>
      constructor
      · intro mem_stabilizer
        let stabilizer := componentStabilizer ((commutingGraph group).connectedComponentMk first)
        obtain ⟨sylow, first_mem⟩ := exists_sylow_containing_involution first
        have sylow_le : (sylow : Subgroup group) ≤ stabilizer :=
          (sylow : Subgroup group).le_normalizer.trans
            (sylow_normalizer_le_componentStabilizer sylow first first_mem)
        let internal_involution : Involution stabilizer :=
          ⟨⟨involution.val, mem_stabilizer⟩, by
            rw [← Subgroup.orderOf_coe]; exact involution.property⟩
        obtain ⟨internal_sylow, internal_mem⟩ :=
          exists_sylow_containing_involution internal_involution
        obtain ⟨conjugator, conjugates⟩ :=
          MulAction.exists_smul_eq stabilizer internal_sylow (sylow.subtype sylow_le)
        have conjugated_mem :=
          involution_smul_mem_sylow conjugator internal_sylow internal_involution internal_mem
        rw [conjugates] at conjugated_mem
        change (conjugator • internal_involution).val ∈
          ((sylow.subtype sylow_le) : Subgroup stabilizer) at conjugated_mem
        rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf] at conjugated_mem
        have ambient_mem : (conjugator.val • involution).val ∈ sylow := conjugated_mem
        have component_eq := SimpleGraph.ConnectedComponent.sound
          (two_subgroup_reachable (sylow : Subgroup group) sylow.isPGroup'
            (conjugator.val • involution) first ambient_mem first_mem)
        rw [← componentMk_smul] at component_eq
        have fixed : conjugator.val • (commutingGraph group).connectedComponentMk first =
            (commutingGraph group).connectedComponentMk first := conjugator.property
        rw [← fixed] at component_eq
        exact (MulAction.injective conjugator.val) component_eq
      · intro component_eq
        rw [← component_eq]
        exact involution_mem_componentStabilizer involution

theorem componentStabilizer_smul {group : Type*} [Group group]
    (conjugator : group) (component : Component group) :
    componentStabilizer (conjugator • component) =
      (componentStabilizer component).map (MulAut.conj conjugator).toMonoidHom :=
  MulAction.stabilizer_smul_eq_stabilizer_map_conj conjugator component

theorem distinct_componentStabilizers_odd_intersection {group : Type*} [Group group]
    [Finite group] (first second : Component group) (distinct : first ≠ second) :
    Odd (Nat.card ↥(componentStabilizer first ⊓ componentStabilizer second)) := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  by_contra not_odd
  have divides := (Nat.not_odd_iff_even.mp not_odd).two_dvd
  obtain ⟨element, element_order⟩ := exists_prime_orderOf_dvd_card' 2 divides
  let involution : Involution group :=
    ⟨element.val, by rw [Subgroup.orderOf_coe]; exact element_order⟩
  have first_component :=
    (componentStabilizer_involution_iff first involution).mp element.property.1
  have second_component :=
    (componentStabilizer_involution_iff second involution).mp element.property.2
  exact distinct (first_component.symm.trans second_component)

theorem componentStabilizer_odd_conjugate_intersection {group : Type*} [Group group]
    [Finite group] (component : Component group) (conjugator : group)
    (not_mem : conjugator ∉ componentStabilizer component) :
    Odd (Nat.card ↥(componentStabilizer component ⊓
      (componentStabilizer component).map (MulAut.conj conjugator).toMonoidHom)) := by
  rw [← componentStabilizer_smul]
  apply distinct_componentStabilizers_odd_intersection
  intro equal_components
  exact not_mem equal_components.symm

theorem componentStabilizer_even {group : Type*} [Group group] [Finite group]
    (component : Component group) : Even (Nat.card (componentStabilizer component)) := by
  induction component using SimpleGraph.ConnectedComponent.ind with
  | h involution =>
      apply even_iff_two_dvd.mpr
      rw [← involution.property]
      exact Subgroup.orderOf_dvd_natCard _ (involution_mem_componentStabilizer involution)

theorem componentStabilizer_odd_index {group : Type*} [Group group] [Finite group]
    (component : Component group) : Odd (componentStabilizer component).index := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  induction component using SimpleGraph.ConnectedComponent.ind with
  | h involution =>
      obtain ⟨sylow, contains⟩ := componentStabilizer_contains_sylow involution
      by_contra not_odd
      exact sylow.not_dvd_index
        ((Nat.not_odd_iff_even.mp not_odd).two_dvd.trans
          (Subgroup.index_dvd_of_le contains))

theorem componentStabilizer_ne_top {group : Type*} [Group group] [Finite group]
    (component : Component group) (disconnected : ∃ other : Component group, other ≠ component) :
    componentStabilizer component ≠ ⊤ := by
  intro equal_top
  obtain ⟨other, distinct⟩ := disconnected
  obtain ⟨conjugator, conjugates⟩ := components_transitive component other
  have mem_stabilizer : conjugator ∈ componentStabilizer component := by
    rw [equal_top]
    trivial
  exact distinct (conjugates.symm.trans mem_stabilizer)

@[expose] def StronglyEmbedded {group : Type*} [Group group] (subgroup : Subgroup group) : Prop :=
  subgroup ≠ ⊤ ∧ Even (Nat.card subgroup) ∧
    ∀ conjugator : group, conjugator ∉ subgroup →
      Odd (Nat.card ↥(subgroup ⊓ subgroup.map (MulAut.conj conjugator).toMonoidHom))

theorem componentStabilizer_stronglyEmbedded {group : Type*} [Group group] [Finite group]
    (component : Component group) (disconnected : ∃ other : Component group, other ≠ component) :
    StronglyEmbedded (componentStabilizer component) := by
  exact ⟨componentStabilizer_ne_top component disconnected, componentStabilizer_even component,
    componentStabilizer_odd_conjugate_intersection component⟩

theorem stronglyEmbedded_right_conjugate_iff {group : Type*} [Group group]
    (subgroup : Subgroup group) :
    StronglyEmbedded subgroup ↔ subgroup ≠ ⊤ ∧ Even (Nat.card subgroup) ∧
      ∀ conjugator : group, conjugator ∉ subgroup →
        Odd (Nat.card ↥(subgroup ⊓ subgroup.map (MulAut.conj conjugator⁻¹).toMonoidHom)) := by
  constructor
  · rintro ⟨proper, even_order, intersections⟩
    refine ⟨proper, even_order, ?_⟩
    intro conjugator not_mem
    exact intersections conjugator⁻¹ (fun mem_inverse =>
      not_mem (subgroup.inv_mem_iff.mp mem_inverse))
  · rintro ⟨proper, even_order, intersections⟩
    refine ⟨proper, even_order, ?_⟩
    intro conjugator not_mem
    simpa only [inv_inv] using intersections conjugator⁻¹ (fun mem_inverse =>
      not_mem (subgroup.inv_mem_iff.mp mem_inverse))

theorem stronglyEmbedded_involution_conjugator_mem {group : Type*} [Group group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup)
    (involution : Involution group) (mem_subgroup : involution.val ∈ subgroup)
    (conjugator : group) (conjugated_mem : (conjugator • involution).val ∈ subgroup) :
    conjugator ∈ subgroup := by
  by_contra not_mem
  have odd_intersection := strong.2.2 conjugator not_mem
  have mem_intersection : (conjugator • involution).val ∈
      subgroup ⊓ subgroup.map (MulAut.conj conjugator).toMonoidHom :=
    ⟨conjugated_mem, Subgroup.mem_map_of_mem _ mem_subgroup⟩
  have divides := Subgroup.orderOf_dvd_natCard _ mem_intersection
  rw [(conjugator • involution).property] at divides
  exact odd_intersection.not_two_dvd_nat divides

theorem stronglyEmbedded_centralizer_le {group : Type*} [Group group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup)
    (involution : Involution group) (mem_subgroup : involution.val ∈ subgroup) :
    Subgroup.centralizer ({involution.val} : Set group) ≤ subgroup := by
  intro conjugator centralizes
  apply stronglyEmbedded_involution_conjugator_mem subgroup strong involution mem_subgroup
    conjugator
  have commuting : involution.val * conjugator = conjugator * involution.val :=
    Subgroup.mem_centralizer_iff.mp centralizes involution.val (by simp)
  rw [involution_smul_val, ← commuting, mul_assoc, mul_inv_cancel, mul_one]
  exact mem_subgroup

theorem stronglyEmbedded_reachable_mem {group : Type*} [Group group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup)
    (first second : Involution group) (first_mem : first.val ∈ subgroup)
    (reachable : (commutingGraph group).Reachable first second) : second.val ∈ subgroup := by
  apply reachable.elim
  intro walk
  clear reachable
  induction walk with
  | nil => exact first_mem
  | @cons first next last adjacent tail induction =>
      apply induction
      apply stronglyEmbedded_centralizer_le subgroup strong first first_mem
      rw [Subgroup.mem_centralizer_iff]
      intro element element_mem
      have equal_element : element = first.val := by simpa using element_mem
      rw [equal_element]
      exact adjacent.2.eq

theorem stronglyEmbedded_not_preconnected {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup) :
    ¬ (commutingGraph group).Preconnected := by
  classical
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨element, element_order⟩ := exists_prime_orderOf_dvd_card' 2 strong.2.1.two_dvd
  let involution : Involution group :=
    ⟨element.val, by rw [Subgroup.orderOf_coe]; exact element_order⟩
  have outside : ∃ conjugator : group, conjugator ∉ subgroup := by
    by_contra no_outside
    push Not at no_outside
    exact strong.1 (subgroup.eq_top_iff'.mpr no_outside)
  obtain ⟨conjugator, not_mem⟩ := outside
  intro preconnected
  have conjugated_mem := stronglyEmbedded_reachable_mem subgroup strong involution
    (conjugator • involution) element.property (preconnected _ _)
  exact not_mem (stronglyEmbedded_involution_conjugator_mem subgroup strong involution
    element.property conjugator conjugated_mem)

theorem not_preconnected_iff_exists_stronglyEmbedded {group : Type*} [Group group]
    [Finite group] : ¬ (commutingGraph group).Preconnected ↔
      ∃ subgroup : Subgroup group, StronglyEmbedded subgroup := by
  classical
  constructor
  · intro not_preconnected
    change ¬ ∀ first second : Involution group,
      (commutingGraph group).Reachable first second at not_preconnected
    push Not at not_preconnected
    obtain ⟨first, second, not_reachable⟩ := not_preconnected
    refine ⟨componentStabilizer ((commutingGraph group).connectedComponentMk first),
      componentStabilizer_stronglyEmbedded _ ?_⟩
    refine ⟨(commutingGraph group).connectedComponentMk second, ?_⟩
    intro equal_components
    exact not_reachable (SimpleGraph.ConnectedComponent.exact equal_components.symm)
  · rintro ⟨subgroup, strong⟩
    exact stronglyEmbedded_not_preconnected subgroup strong

theorem not_connected_iff_exists_stronglyEmbedded {group : Type*} [Group group]
    [Finite group] (even_order : Even (Nat.card group)) :
    ¬ (commutingGraph group).Connected ↔
      ∃ subgroup : Subgroup group, StronglyEmbedded subgroup := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨element, element_order⟩ := exists_prime_orderOf_dvd_card' 2 even_order.two_dvd
  have vertices_nonempty : Nonempty (Involution group) := ⟨⟨element, element_order⟩⟩
  rw [SimpleGraph.connected_iff, and_iff_left vertices_nonempty]
  exact not_preconnected_iff_exists_stronglyEmbedded

instance componentIsPretransitive (group : Type*) [Group group] [Finite group] :
    MulAction.IsPretransitive group (Component group) := ⟨components_transitive⟩

theorem componentStabilizer_index_eq_card {group : Type*} [Group group] [Finite group]
    (component : Component group) :
    (componentStabilizer component).index = Nat.card (Component group) := by
  change (MulAction.stabilizer group component).index = _
  rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ, Set.ncard_univ]

theorem componentStabilizer_injective {group : Type*} [Group group] [Finite group] :
    Function.Injective (componentStabilizer (group := group)) := by
  intro first second equal_stabilizers
  induction first using SimpleGraph.ConnectedComponent.ind with
  | h involution =>
      have mem_second := involution_mem_componentStabilizer involution
      rw [equal_stabilizers] at mem_second
      exact (componentStabilizer_involution_iff second involution).mp mem_second

theorem involution_unique_fixed_component {group : Type*} [Group group] [Finite group]
    (involution : Involution group) :
    ∃! component : Component group, involution.val • component = component := by
  have fixed_iff (component : Component group) :
      involution.val • component = component ↔
        (commutingGraph group).connectedComponentMk involution = component :=
    componentStabilizer_involution_iff component involution
  refine ⟨(commutingGraph group).connectedComponentMk involution,
    (fixed_iff _).mpr rfl, ?_⟩
  intro component fixed
  exact ((fixed_iff component).mp fixed).symm

theorem simple_component_action_injective {group : Type*} [Group group] [Finite group]
    [IsSimpleGroup group] (component : Component group)
    (disconnected : ∃ other : Component group, other ≠ component) :
    Function.Injective (MulAction.toPermHom group (Component group)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rcases CFSG.eq_bot_or_eq_top_of_normal
    (MulAction.toPermHom group (Component group)).ker inferInstance with
    kernel_bot | kernel_top
  · exact kernel_bot
  · exfalso
    apply componentStabilizer_ne_top component disconnected
    apply (componentStabilizer component).eq_top_iff'.mpr
    intro element
    have mem_kernel : element ∈ (MulAction.toPermHom group (Component group)).ker := by
      rw [kernel_top]
      trivial
    exact congrArg (fun permutation : Equiv.Perm (Component group) => permutation component)
      mem_kernel

theorem involution_stabilizer_eq_centralizer {group : Type*} [Group group]
    (involution : Involution group) :
    MulAction.stabilizer group involution = Subgroup.centralizer ({involution.val} : Set group) := by
  ext element
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro fixed other other_mem
    have equal_other : other = involution.val := by simpa using other_mem
    rw [equal_other]
    have underlying := congrArg (fun vertex : Involution group => vertex.val * element) fixed
    simpa only [involution_smul_val, mul_assoc, inv_mul_cancel, mul_one] using underlying.symm
  · intro centralizes
    apply Subtype.ext
    rw [involution_smul_val,
      ← centralizes involution.val (by simp), mul_assoc, mul_inv_cancel, mul_one]

end CFSG.OrderReductions.InvolutionGraph
