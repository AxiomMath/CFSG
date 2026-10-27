module

public import CFSG.Assembly.OrderReductions.TwoPointSylow

public section

namespace CFSG.OrderReductions.MaximalThreePoint

open CFSG.OrderReductions.InvolutionGraph
open CFSG.OrderReductions.TwoPointInvolutions
open CFSG.OrderReductions.FixedPairSylow

@[expose] def ThreePointPrime {group points : Type*} [Group group] [MulAction group points]
    (prime : ℕ) (subgroup : Subgroup group) : Prop :=
  IsPGroup prime subgroup ∧ 3 ≤ Nat.card (MulAction.fixedPoints subgroup points)

theorem fixedPoints_le_two_eq_pair {group points : Type*} [Group group]
    [MulAction group points] [Finite points] (subgroup : Subgroup group)
    (first second : points) (distinct : first ≠ second)
    (first_fixed : first ∈ MulAction.fixedPoints subgroup points)
    (second_fixed : second ∈ MulAction.fixedPoints subgroup points)
    (small : Nat.card (MulAction.fixedPoints subgroup points) ≤ 2) :
    MulAction.fixedPoints subgroup points = {first, second} := by
  have pair_le : ({first, second} : Set points) ⊆ MulAction.fixedPoints subgroup points := by
    intro point mem_pair
    rcases Set.mem_insert_iff.mp mem_pair with equal_first | equal_second
    · exact equal_first ▸ first_fixed
    · rw [Set.mem_singleton_iff] at equal_second
      exact equal_second ▸ second_fixed
  by_contra unequal
  have proper : ({first, second} : Set points) ⊂ MulAction.fixedPoints subgroup points :=
    lt_of_le_of_ne pair_le (Ne.symm unequal)
  have card_lt := (Set.toFinite (MulAction.fixedPoints subgroup points)).card_lt_card proper
  have pair_card : Nat.card ({first, second} : Set points) = 2 := by
    rw [Nat.card_coe_set_eq, Set.ncard_pair distinct]
  rw [pair_card] at card_lt
  omega

theorem maximal_extension_fixed_pair {group points : Type*} [Group group]
    [MulAction group points] [Finite points] (prime : ℕ)
    (subgroup : Subgroup group) (maximal : Maximal (ThreePointPrime (points := points) prime) subgroup)
    (larger : Subgroup group) (larger_prime : IsPGroup prime larger)
    (strictly_larger : subgroup < larger) (first second : points) (distinct : first ≠ second)
    (first_fixed : first ∈ MulAction.fixedPoints larger points)
    (second_fixed : second ∈ MulAction.fixedPoints larger points) :
    MulAction.fixedPoints larger points = {first, second} := by
  have small : Nat.card (MulAction.fixedPoints larger points) ≤ 2 := by
    by_contra not_small
    have larger_three : ThreePointPrime (points := points) prime larger :=
      ⟨larger_prime, by omega⟩
    exact strictly_larger.ne (maximal.eq_of_le larger_three strictly_larger.le)
  exact fixedPoints_le_two_eq_pair larger first second distinct first_fixed second_fixed small

theorem involution_fixed_component_unique {group : Type*} [Group group] [Finite group]
    (involution : Involution group) (first second : Component group)
    (first_fixed : involution.val • first = first)
    (second_fixed : involution.val • second = second) : first = second := by
  obtain ⟨component, _, unique⟩ := involution_unique_fixed_component involution
  exact (unique first first_fixed).trans (unique second second_fixed).symm

theorem maximal_pair_normalizer_flip {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (subgroup : Subgroup group)
    (maximal : Maximal (ThreePointPrime (points := Component group) prime) subgroup)
    (first second : Component group) (distinct : first ≠ second)
    (first_fixed : first ∈ MulAction.fixedPoints subgroup (Component group))
    (second_fixed : second ∈ MulAction.fixedPoints subgroup (Component group))
    (same_orbit : ∃ element : Subgroup.normalizer (subgroup : Set group),
      element.val • first = second) :
    ∃ flip : Involution group,
      flip.val ∈ Subgroup.normalizer (subgroup : Set group) ∧
      flip.val • first = second ∧ flip.val • second = first := by
  have prime_group := maximal.prop.1
  have subgroup_le : subgroup ≤ pairSubgroup first second := by
    intro element mem_subgroup
    exact ⟨MulAction.mem_fixedPoints.mp first_fixed ⟨element, mem_subgroup⟩,
      MulAction.mem_fixedPoints.mp second_fixed ⟨element, mem_subgroup⟩⟩
  by_cases is_sylow : ∃ sylow : Sylow prime (pairSubgroup first second),
      (sylow : Subgroup (pairSubgroup first second)).map
        (pairSubgroup first second).subtype = subgroup
  · obtain ⟨sylow, image_eq⟩ := is_sylow
    obtain ⟨flip, normalizes, first_moves, second_moves⟩ :=
      CFSG.OrderReductions.TwoPointSylow.exists_sylow_normalizing_flip prime first second distinct sylow
    rw [image_eq] at normalizes
    exact ⟨flip, normalizes, first_moves, second_moves⟩
  · obtain ⟨larger, larger_prime, strictly_larger, larger_le⟩ :=
      exists_larger_prime_subgroup_in_normalizer_within prime subgroup
        (pairSubgroup first second) subgroup_le prime_group is_sylow
    have larger_first : first ∈ MulAction.fixedPoints larger (Component group) := by
      apply MulAction.mem_fixedPoints.mpr
      intro element
      exact (larger_le element.property).2.1
    have larger_second : second ∈ MulAction.fixedPoints larger (Component group) := by
      apply MulAction.mem_fixedPoints.mpr
      intro element
      exact (larger_le element.property).2.2
    have fixed_pair := maximal_extension_fixed_pair prime subgroup maximal larger larger_prime
      strictly_larger first second distinct larger_first larger_second
    let normalizer := Subgroup.normalizer (subgroup : Set group)
    have larger_normalizer : larger ≤ normalizer := larger_le.trans inf_le_left
    have restricted_prime : IsPGroup prime (larger.subgroupOf normalizer) :=
      larger_prime.of_equiv (Subgroup.subgroupOfEquivOfLe larger_normalizer).symm
    have restricted_fixed : MulAction.fixedPoints (larger.subgroupOf normalizer)
        (Component group) = {first, second} := by
      rw [← fixedPoints_map_subtype normalizer,
        Subgroup.map_subgroupOf_eq_of_le larger_normalizer]
      exact fixed_pair
    obtain ⟨flipper, first_moves, second_moves⟩ := exists_fixed_pair_orbit_flip prime
      (larger.subgroupOf normalizer) restricted_prime first second distinct restricted_fixed
      same_orbit
    obtain ⟨exponent, power_order, power_first, power_second⟩ := involution_power_flips_pair
      involution_fixed_component_unique flipper.val first second distinct first_moves second_moves
    exact ⟨⟨flipper.val ^ exponent, power_order⟩,
      normalizer.pow_mem flipper.property exponent, power_first, power_second⟩

theorem maximal_normalizer_moves_fixed_point {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (subgroup : Subgroup group)
    (maximal : Maximal (ThreePointPrime (points := Component group) prime) subgroup) :
    ∃ element : Subgroup.normalizer (subgroup : Set group),
      ∃ point ∈ MulAction.fixedPoints subgroup (Component group), element.val • point ≠ point := by
  classical
  by_contra no_moves
  push Not at no_moves
  let fixed := MulAction.fixedPoints subgroup (Component group)
  let := Fintype.ofFinite fixed
  have large : 1 < Fintype.card fixed := by
    rw [← Nat.card_eq_fintype_card]
    have three : 3 ≤ Nat.card fixed := maximal.prop.2
    omega
  obtain ⟨first_vertex, second_vertex, vertices_distinct⟩ := Fintype.one_lt_card_iff.mp large
  let first := first_vertex.val
  let second := second_vertex.val
  have distinct : first ≠ second := fun equal_points =>
    vertices_distinct (Subtype.ext equal_points)
  have subgroup_le : subgroup ≤ pairSubgroup first second := by
    intro element mem_subgroup
    exact ⟨MulAction.mem_fixedPoints.mp first_vertex.property ⟨element, mem_subgroup⟩,
      MulAction.mem_fixedPoints.mp second_vertex.property ⟨element, mem_subgroup⟩⟩
  by_cases is_sylow : ∃ sylow : Sylow prime (pairSubgroup first second),
      (sylow : Subgroup (pairSubgroup first second)).map
        (pairSubgroup first second).subtype = subgroup
  · obtain ⟨sylow, image_eq⟩ := is_sylow
    obtain ⟨flip, normalizes, first_moves, _⟩ :=
      CFSG.OrderReductions.TwoPointSylow.exists_sylow_normalizing_flip prime first second distinct sylow
    rw [image_eq] at normalizes
    have fixes := no_moves ⟨flip.val, normalizes⟩ first first_vertex.property
    exact distinct (fixes.symm.trans first_moves)
  · obtain ⟨larger, larger_prime, strictly_larger, larger_le⟩ :=
      exists_larger_prime_subgroup_in_normalizer_within prime subgroup
        (pairSubgroup first second) subgroup_le maximal.prop.1 is_sylow
    have all_fixed : fixed ⊆ MulAction.fixedPoints larger (Component group) := by
      intro point mem_fixed
      apply MulAction.mem_fixedPoints.mpr
      intro element
      exact no_moves ⟨element.val, (larger_le element.property).1⟩ point mem_fixed
    have card_le := Nat.card_le_card_of_injective
      (Set.inclusion all_fixed) (Set.inclusion_injective all_fixed)
    have larger_three : ThreePointPrime (points := Component group) prime larger :=
      ⟨larger_prime, maximal.prop.2.trans card_le⟩
    exact strictly_larger.ne (maximal.eq_of_le larger_three strictly_larger.le)

theorem maximal_normalizer_even {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (subgroup : Subgroup group)
    (maximal : Maximal (ThreePointPrime (points := Component group) prime) subgroup) :
    Even (Nat.card (Subgroup.normalizer (subgroup : Set group))) := by
  obtain ⟨element, first, first_fixed, moves⟩ :=
    maximal_normalizer_moves_fixed_point prime subgroup maximal
  have second_fixed := normalizer_preserves_fixedPoints subgroup element.val element.property
    first_fixed
  obtain ⟨flip, normalizes, _, _⟩ := maximal_pair_normalizer_flip prime subgroup maximal
    first (element.val • first) moves.symm first_fixed second_fixed ⟨element, rfl⟩
  have divides := Subgroup.orderOf_dvd_natCard
    (Subgroup.normalizer (subgroup : Set group)) normalizes
  rw [flip.property] at divides
  exact even_iff_two_dvd.mpr divides

end CFSG.OrderReductions.MaximalThreePoint
