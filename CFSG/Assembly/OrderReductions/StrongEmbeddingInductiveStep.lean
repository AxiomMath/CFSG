module

public import CFSG.Assembly.OrderReductions.SolvableDoubleTransitivity

public section

namespace CFSG.OrderReductions.StrongEmbeddingInductiveStep

universe group_universe

open CFSG.OrderReductions.InvolutionGraph

theorem every_component_has_four {group : Type*} [Group group] [Finite group]
    (first second : Involution group) (distinct : first ≠ second) (commutes : Commute first.val second.val)
    (point : Component group) : ∃ first second : Involution group,
      first ≠ second ∧ Commute first.val second.val ∧
        first.val ∈ componentStabilizer point ∧ second.val ∈ componentStabilizer point := by
  let base := (commutingGraph group).connectedComponentMk first
  obtain ⟨acting, moves⟩ := components_transitive base point
  refine ⟨acting • first, acting • second, ?_, commutes.map (MulAut.conj acting).toMonoidHom, ?_, ?_⟩
  · intro equal
    exact distinct (smul_left_cancel acting equal)
  · apply (componentStabilizer_involution_iff point (acting • first)).mpr
    rw [← componentMk_smul]
    exact moves
  · apply (componentStabilizer_involution_iff point (acting • second)).mpr
    rw [← componentMk_smul]
    have components_eq := SimpleGraph.ConnectedComponent.sound (reachable_of_commute first second commutes)
    rw [← components_eq]
    exact moves

theorem componentStabilizer_le_stronglyEmbedded {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup)
    (involution : Involution group) (membership : involution.val ∈ subgroup) :
    componentStabilizer ((commutingGraph group).connectedComponentMk involution) ≤ subgroup := by
  intro acting fixed_component
  have component_eq : (commutingGraph group).connectedComponentMk (acting • involution) =
      (commutingGraph group).connectedComponentMk involution := by
    rw [← componentMk_smul]
    exact fixed_component
  have conjugated_mem := stronglyEmbedded_reachable_mem subgroup strong involution (acting • involution)
    membership (SimpleGraph.ConnectedComponent.exact component_eq.symm)
  exact stronglyEmbedded_involution_conjugator_mem subgroup strong involution membership acting conjugated_mem

theorem stronglyEmbedded_eq_componentStabilizer_of_double_transitive {group : Type*} [Group group]
    [Finite group] (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup)
    (involution : Involution group) (membership : involution.val ∈ subgroup)
    (two_transitive : MulAction.IsMultiplyPretransitive group (Component group) 2) :
    subgroup = componentStabilizer ((commutingGraph group).connectedComponentMk involution) := by
  let point := (commutingGraph group).connectedComponentMk involution
  have contains := componentStabilizer_le_stronglyEmbedded subgroup strong involution membership
  have point_proper : componentStabilizer point ≠ ⊤ := by
    intro equal_top
    exact strong.1 (top_unique (equal_top ▸ contains))
  have : Nontrivial (Component group) := by
    obtain ⟨acting, outside⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr point_proper)
    apply nontrivial_of_ne point (acting • point)
    intro equal
    exact outside.2 equal.symm
  have : MulAction.IsPreprimitive group (Component group) :=
    MulAction.isPreprimitive_of_is_two_pretransitive two_transitive
  have coatom := MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive group point
  exact (coatom.le_iff_eq strong.1).mp contains

theorem double_transitive_of_odd_solvable_and_even_point_rules
    {group : Type group_universe} [Group group] [Finite group]
    (induction_hypothesis : ∀ (smaller : Type group_universe) [Group smaller] [Finite smaller],
      Nat.card smaller < Nat.card group →
      ∀ first second : Involution smaller, first ≠ second → Commute first.val second.val →
        ∀ subgroup : Subgroup smaller, StronglyEmbedded subgroup →
          MulAction.IsMultiplyPretransitive smaller (CFSG.OrderReductions.StrongEmbedding.Conjugates subgroup) 2)
    (first second : Involution group) (distinct : first ≠ second) (commutes : Commute first.val second.val)
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup)
    (odd_solvable : ∀ subgroup : Subgroup group, Odd (Nat.card subgroup) → Group.IsSolvable subgroup)
    (ambient_rule : ∀ prime : ℕ, Nat.Prime prime → CFSG.OrderReductions.EmptyRegularity.EvenPointRule (group := group) prime)
    (normalizer_rule : ∀ normal : Subgroup group, ∀ prime : ℕ, Nat.Prime prime →
      CFSG.OrderReductions.EmptyRegularity.EvenPointRule (group := Subgroup.normalizer (normal : Set group)) prime) :
    MulAction.IsMultiplyPretransitive group (CFSG.OrderReductions.StrongEmbedding.Conjugates subgroup) 2 := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨element, element_order⟩ := exists_prime_orderOf_dvd_card' 2 strong.2.1.two_dvd
  let involution : Involution group := ⟨element.val, (Subgroup.orderOf_coe element).trans element_order⟩
  let point := (commutingGraph group).connectedComponentMk involution
  have contains := componentStabilizer_le_stronglyEmbedded subgroup strong involution element.property
  have point_proper : componentStabilizer point ≠ ⊤ := by
    intro equal_top
    exact strong.1 (top_unique (equal_top ▸ contains))
  have point_strong : StronglyEmbedded (componentStabilizer point) :=
    ⟨point_proper, componentStabilizer_even point, componentStabilizer_odd_conjugate_intersection point⟩
  have degree : 3 ≤ Nat.card (Component group) := by
    rw [Nat.card_congr (CFSG.OrderReductions.InternalComponents.componentsEquivConjugates point)]
    exact CFSG.OrderReductions.StrongEmbedding.conjugates_card_ge_three _ point_strong
  have two_transitive := CFSG.OrderReductions.SolvableDoubleTransitivity.double_transitive_inductive_step
    induction_hypothesis point degree (every_component_has_four first second distinct commutes) odd_solvable
    ambient_rule normalizer_rule
  have subgroup_eq := stronglyEmbedded_eq_componentStabilizer_of_double_transitive subgroup strong involution
    element.property two_transitive
  rw [subgroup_eq]
  exact (CFSG.OrderReductions.InternalComponents.components_two_transitive_iff_conjugates point).mp two_transitive

end CFSG.OrderReductions.StrongEmbeddingInductiveStep
