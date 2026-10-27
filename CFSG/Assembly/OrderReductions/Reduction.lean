module

public import Mathlib
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
public import CFSG.Open.OrderForm
public import CFSG.Assembly.OrderReductions.Helpers
public import CFSG.Assembly.OrderReductions.InvolutionGraph
public import CFSG.Assembly.OrderReductions.PermutationReduction
public import CFSG.Assembly.OrderReductions.StrongEmbedding

public section

open CFSG.Open

namespace CFSG.OrderReductions.Reduction

@[expose] def ProperSimpleSectionOrders (group : Type*) [Group group] : Prop :=
  ∀ (subgroup : Subgroup group), subgroup ≠ ⊤ →
    ∀ (kernel : Subgroup subgroup) [kernel.Normal] [IsSimpleGroup (subgroup ⧸ kernel)],
      Nat.card (subgroup ⧸ kernel) ∈ cfsgOrders

@[expose] def IsMinimalCounterexample (group : Type) [Group group] : Prop :=
  Nat.card group ∉ cfsgOrders ∧
    ∀ (smaller_group : Type) [Group smaller_group] [Finite smaller_group]
      [IsSimpleGroup smaller_group], Nat.card smaller_group < Nat.card group →
        Nat.card smaller_group ∈ cfsgOrders

theorem exists_minimal_counterexample (group : Type) [Group group] [Finite group]
    [IsSimpleGroup group] (unlisted : Nat.card group ∉ cfsgOrders) :
    ∃ (minimal_group : Type) (_group_structure : Group minimal_group),
      Finite minimal_group ∧ IsSimpleGroup minimal_group ∧
        IsMinimalCounterexample minimal_group := by
  classical
  let counterexample_order : ℕ → Prop := fun order =>
    ∃ (candidate : Type) (group_structure : Group candidate),
      Finite candidate ∧ IsSimpleGroup candidate ∧ Nat.card candidate = order ∧
        Nat.card candidate ∉ cfsgOrders
  have some_order : ∃ order, counterexample_order order :=
    ⟨Nat.card group, group, inferInstance, inferInstance, inferInstance, rfl, unlisted⟩
  obtain ⟨minimal_group, group_structure, finite_group, simple_group, order_eq, unlisted_order⟩ :=
    Nat.find_spec some_order
  let _ : Group minimal_group := group_structure
  let _ : Finite minimal_group := finite_group
  let _ : IsSimpleGroup minimal_group := simple_group
  refine ⟨minimal_group, group_structure, finite_group, simple_group, unlisted_order, ?_⟩
  intro smaller_group group_instance finite_instance simple_instance smaller
  by_contra smaller_unlisted
  have forbidden_order : counterexample_order (Nat.card smaller_group) :=
    ⟨smaller_group, group_instance, finite_instance, simple_instance, rfl, smaller_unlisted⟩
  exact Nat.find_min some_order (by simpa only [← order_eq] using smaller) forbidden_order

theorem properSimpleSectionOrders_of_card_mem (group : Type*) [Group group]
    (section_orders : ∀ (subgroup : Subgroup group) (kernel : Subgroup subgroup)
      [kernel.Normal] [IsSimpleGroup (subgroup ⧸ kernel)],
        Nat.card (subgroup ⧸ kernel) ∈ cfsgOrders) : ProperSimpleSectionOrders group := by
  intro subgroup _ kernel _ _
  exact section_orders subgroup kernel

theorem proper_subgroup_card_lt (group : Type*) [Group group] [Finite group]
    (subgroup : Subgroup group) (proper : subgroup ≠ ⊤) :
    Nat.card subgroup < Nat.card group := by
  apply Nat.lt_of_le_of_ne (subgroup.card_le_card_group)
  intro equal_card
  exact proper (subgroup.eq_top_of_card_eq equal_card)

theorem proper_simple_section_card_lt (group : Type*) [Group group] [Finite group]
    (subgroup : Subgroup group) (proper : subgroup ≠ ⊤) (kernel : Subgroup subgroup) :
    Nat.card (subgroup ⧸ kernel) < Nat.card group := by
  have quotient_card_le : Nat.card (subgroup ⧸ kernel) ≤ Nat.card subgroup :=
    Nat.le_of_dvd (Nat.card_pos) (Subgroup.card_quotient_dvd_card kernel)
  exact lt_of_le_of_lt quotient_card_le (proper_subgroup_card_lt group subgroup proper)

theorem properSimpleSectionOrders_of_smaller_orders (group : Type) [Group group]
    [Finite group]
    (smaller_orders : ∀ (simple_section : Type) [Group simple_section] [Finite simple_section]
      [IsSimpleGroup simple_section], Nat.card simple_section < Nat.card group →
        Nat.card simple_section ∈ cfsgOrders) : ProperSimpleSectionOrders group := by
  intro subgroup proper kernel _ _
  exact smaller_orders (subgroup ⧸ kernel)
    (proper_simple_section_card_lt group subgroup proper kernel)

theorem minimal_counterexample_proper_simple_sections (group : Type) [Group group]
    [Finite group] (minimal : IsMinimalCounterexample group) :
    ProperSimpleSectionOrders group :=
  properSimpleSectionOrders_of_smaller_orders group minimal.2

theorem minimal_counterexample_noncommutative (group : Type) [Group group]
    [IsSimpleGroup group] (minimal : IsMinimalCounterexample group) :
    ¬ IsMulCommutative group := by
  intro commutative
  have := commutative
  exact minimal.1 (CFSG.OrderReductions.Helpers.card_mem_cfsgOrders_of_simple_commutative group)

theorem minimal_counterexample_isPerfect (group : Type) [Group group]
    [IsSimpleGroup group] (minimal : IsMinimalCounterexample group) :
    Group.IsPerfect group :=
  CFSG.OrderReductions.Helpers.simple_noncommutative_isPerfect group
    (minimal_counterexample_noncommutative group minimal)

theorem minimal_counterexample_center_eq_bot (group : Type) [Group group]
    [IsSimpleGroup group] (minimal : IsMinimalCounterexample group) :
    Subgroup.center group = ⊥ :=
  CFSG.OrderReductions.Helpers.simple_noncommutative_center_eq_bot group
    (minimal_counterexample_noncommutative group minimal)

theorem minimal_counterexample_not_solvable (group : Type) [Group group]
    [IsSimpleGroup group] (minimal : IsMinimalCounterexample group) :
    ¬ Group.IsSolvable group :=
  CFSG.OrderReductions.Helpers.simple_noncommutative_not_solvable group
    (minimal_counterexample_noncommutative group minimal)

theorem minimal_counterexample_not_prime_power (group : Type) [Group group] [Finite group]
    [IsSimpleGroup group] (minimal : IsMinimalCounterexample group) :
    ¬ IsPrimePow (Nat.card group) := by
  intro prime_power
  exact minimal.1 (CFSG.OrderReductions.Helpers.card_mem_cfsgOrders_of_simple_prime_power group prime_power)

theorem minimal_counterexample_not_squarefree (group : Type) [Group group] [Finite group]
    [IsSimpleGroup group] (minimal : IsMinimalCounterexample group) :
    ¬ Squarefree (Nat.card group) := by
  intro squarefree_order
  exact minimal.1
    (CFSG.OrderReductions.Helpers.card_mem_cfsgOrders_of_simple_squarefree group squarefree_order)

theorem minimal_counterexample_minFac_sylow_not_cyclic (group : Type) [Group group]
    [Finite group] [IsSimpleGroup group] (minimal : IsMinimalCounterexample group)
    (sylow : Sylow (Nat.card group).minFac group) : ¬ IsCyclic sylow :=
  CFSG.OrderReductions.Helpers.simple_noncommutative_minFac_sylow_not_cyclic group
    (minimal_counterexample_noncommutative group minimal) sylow

theorem minimal_counterexample_minFac_sq_dvd_card (group : Type) [Group group]
    [Finite group] [IsSimpleGroup group] (minimal : IsMinimalCounterexample group) :
    (Nat.card group).minFac ^ 2 ∣ Nat.card group :=
  CFSG.OrderReductions.Helpers.simple_noncommutative_minFac_sq_dvd_card group
    (minimal_counterexample_noncommutative group minimal)

theorem minimal_counterexample_four_dvd_card_of_even (group : Type) [Group group]
    [Finite group] [IsSimpleGroup group] (minimal : IsMinimalCounterexample group)
    (even_order : Even (Nat.card group)) : 4 ∣ Nat.card group :=
  CFSG.OrderReductions.Helpers.simple_noncommutative_four_dvd_card_of_even group
    (minimal_counterexample_noncommutative group minimal) even_order

theorem minimal_counterexample_proper_subgroup_index_ge_five (group : Type) [Group group]
    [Finite group] [IsSimpleGroup group] (minimal : IsMinimalCounterexample group)
    (subgroup : Subgroup group) (proper : subgroup ≠ ⊤) : 5 ≤ subgroup.index := by
  by_contra small_index
  exact minimal.1 (CFSG.OrderReductions.PermutationReduction.simple_card_mem_orders_of_index_le_four
    group subgroup proper (by omega))

theorem minimal_counterexample_proper_subgroup_index_ge_six (group : Type) [Group group]
    [Finite group] [IsSimpleGroup group] (minimal : IsMinimalCounterexample group)
    (subgroup : Subgroup group) (proper : subgroup ≠ ⊤) : 6 ≤ subgroup.index := by
  by_contra small_index
  exact minimal.1 (CFSG.OrderReductions.PermutationReduction.simple_card_mem_orders_of_index_le_five
    group subgroup proper (by omega))

theorem minimal_counterexample_proper_subgroup_index_ge_seven (group : Type) [Group group]
    [Finite group] [IsSimpleGroup group] (minimal : IsMinimalCounterexample group)
    (subgroup : Subgroup group) (proper : subgroup ≠ ⊤) : 7 ≤ subgroup.index := by
  by_contra small_index
  exact minimal.1 (CFSG.OrderReductions.PermutationReduction.simple_card_mem_orders_of_index_le_six
    group subgroup proper (by omega))

theorem minimal_counterexample_stronglyEmbedded_conjugates_ge_seven (group : Type)
    [Group group] [Finite group] [IsSimpleGroup group] (minimal : IsMinimalCounterexample group)
    (subgroup : Subgroup group) (strong : CFSG.OrderReductions.InvolutionGraph.StronglyEmbedded subgroup) :
    7 ≤ Nat.card (CFSG.OrderReductions.StrongEmbedding.Conjugates subgroup) := by
  rw [← Nat.card_congr (CFSG.OrderReductions.StrongEmbedding.cosetEquivConjugates subgroup strong),
    ← subgroup.index_eq_card]
  exact minimal_counterexample_proper_subgroup_index_ge_seven group minimal subgroup strong.1

theorem minimal_counterexample_disconnected_component_properties (group : Type)
    [Group group] [Finite group] [IsSimpleGroup group] (minimal : IsMinimalCounterexample group)
    (component : CFSG.OrderReductions.InvolutionGraph.Component group)
    (other_component : ∃ other : CFSG.OrderReductions.InvolutionGraph.Component group, other ≠ component) :
    let stabilizer := CFSG.OrderReductions.InvolutionGraph.componentStabilizer component
    CFSG.OrderReductions.InvolutionGraph.StronglyEmbedded stabilizer ∧ Odd stabilizer.index ∧
      7 ≤ stabilizer.index ∧ ProperSimpleSectionOrders stabilizer := by
  dsimp only
  have strong := CFSG.OrderReductions.InvolutionGraph.componentStabilizer_stronglyEmbedded
    component other_component
  refine ⟨strong, CFSG.OrderReductions.InvolutionGraph.componentStabilizer_odd_index component,
    minimal_counterexample_proper_subgroup_index_ge_seven group minimal _ strong.1, ?_⟩
  apply properSimpleSectionOrders_of_smaller_orders
  intro simple_section _ _ _ smaller
  exact minimal.2 simple_section (smaller.trans (proper_subgroup_card_lt group _ strong.1))

theorem minimal_counterexample_disconnected_component_card_ge_seven (group : Type)
    [Group group] [Finite group] [IsSimpleGroup group] (minimal : IsMinimalCounterexample group)
    (component : CFSG.OrderReductions.InvolutionGraph.Component group)
    (other_component : ∃ other : CFSG.OrderReductions.InvolutionGraph.Component group, other ≠ component) :
    7 ≤ Nat.card (CFSG.OrderReductions.InvolutionGraph.Component group) := by
  rw [← CFSG.OrderReductions.InvolutionGraph.componentStabilizer_index_eq_card component]
  exact minimal_counterexample_proper_subgroup_index_ge_seven group minimal _
    (CFSG.OrderReductions.InvolutionGraph.componentStabilizer_ne_top component other_component)

theorem minimal_counterexample_stronglyEmbedded_index_ge_nine (group : Type)
    [Group group] [Finite group] [IsSimpleGroup group] (minimal : IsMinimalCounterexample group)
    (subgroup : Subgroup group) (strong : CFSG.OrderReductions.InvolutionGraph.StronglyEmbedded subgroup) :
    9 ≤ subgroup.index := by
  have : Group.IsPerfect group := minimal_counterexample_isPerfect group minimal
  have index_bound := minimal_counterexample_proper_subgroup_index_ge_seven
    group minimal subgroup strong.1
  have congruence := CFSG.OrderReductions.StrongEmbedding.perfect_index_mod_four subgroup strong
  omega

theorem minimal_counterexample_disconnected_component_card_ge_nine (group : Type)
    [Group group] [Finite group] [IsSimpleGroup group] (minimal : IsMinimalCounterexample group)
    (component : CFSG.OrderReductions.InvolutionGraph.Component group)
    (other_component : ∃ other : CFSG.OrderReductions.InvolutionGraph.Component group, other ≠ component) :
    9 ≤ Nat.card (CFSG.OrderReductions.InvolutionGraph.Component group) := by
  rw [← CFSG.OrderReductions.InvolutionGraph.componentStabilizer_index_eq_card component]
  exact minimal_counterexample_stronglyEmbedded_index_ge_nine group minimal _
    (CFSG.OrderReductions.InvolutionGraph.componentStabilizer_stronglyEmbedded component other_component)

theorem cfsg_of_no_minimal_counterexample
    (no_minimal : ∀ (group : Type) [Group group] [Finite group] [IsSimpleGroup group],
      ¬ IsMinimalCounterexample group)
    (group : Type) [Group group] [Finite group] [IsSimpleGroup group] :
    Nat.card group ∈ cfsgOrders := by
  classical
  by_contra unlisted
  obtain ⟨minimal_group, group_structure, finite_group, simple_group, minimal⟩ :=
    exists_minimal_counterexample group unlisted
  let _ : Group minimal_group := group_structure
  let _ : Finite minimal_group := finite_group
  let _ : IsSimpleGroup minimal_group := simple_group
  exact no_minimal minimal_group minimal

theorem cfsg_of_proper_simple_section_step
    (classification_step : ∀ (group : Type) [Group group] [Finite group]
      [IsSimpleGroup group], ProperSimpleSectionOrders group →
        Nat.card group ∈ cfsgOrders)
    (group : Type) [Group group] [Finite group] [IsSimpleGroup group] :
    Nat.card group ∈ cfsgOrders := by
  generalize order_eq : Nat.card group = order
  induction order using Nat.strong_induction_on generalizing group with
  | h order induction_hypothesis =>
      rw [← order_eq]
      apply classification_step group
      apply properSimpleSectionOrders_of_smaller_orders
      intro simple_section _ _ _ smaller
      exact induction_hypothesis (Nat.card simple_section)
        (by simpa only [← order_eq] using smaller) simple_section rfl

theorem cfsg_of_noncommutative_step
    (classification_step : ∀ (group : Type) [Group group] [Finite group]
      [IsSimpleGroup group], ¬ IsMulCommutative group → ProperSimpleSectionOrders group →
        Nat.card group ∈ cfsgOrders)
    (group : Type) [Group group] [Finite group] [IsSimpleGroup group] :
    Nat.card group ∈ cfsgOrders := by
  classical
  apply cfsg_of_proper_simple_section_step _ group
  intro candidate _ _ _ proper_sections
  by_cases commutative : IsMulCommutative candidate
  · have := commutative
    exact CFSG.OrderReductions.Helpers.card_mem_cfsgOrders_of_simple_commutative candidate
  · exact classification_step candidate commutative proper_sections

end CFSG.OrderReductions.Reduction
