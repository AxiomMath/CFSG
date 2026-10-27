module

public import CFSG.Assembly.OrderReductions.LocalRegularity

public section

namespace CFSG.OrderReductions.EmptyRegularity

open CFSG.OrderReductions.InvolutionGraph
open CFSG.OrderReductions.TwoPointInvolutions
open CFSG.OrderReductions.PrimeRegular

@[expose] def EvenPointRule {group : Type*} [Group group] (prime : ℕ) : Prop :=
  ∀ subgroup : Subgroup group,
    Maximal (CFSG.OrderReductions.MaximalThreePoint.ThreePointPrime (points := Component group) prime) subgroup →
    ∃ point ∈ MulAction.fixedPoints subgroup (Component group),
      Even (Nat.card ↥(Subgroup.normalizer (subgroup : Set group) ⊓ componentStabilizer point))

@[expose] def NoRegularPair {group : Type*} [Group group] (prime : ℕ) : Prop :=
  ∀ first second : Component group, first ≠ second →
    ¬ PRegular prime (pairSubgroup first second) (componentStabilizer first)

theorem pair_sylow_fixed_pair_of_no_regular {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (even_point_rule : EvenPointRule (group := group) prime)
    (no_regular : NoRegularPair (group := group) prime)
    (first second : Component group) (distinct : first ≠ second)
    (sylow : Sylow prime (pairSubgroup first second)) :
    MulAction.fixedPoints ((sylow : Subgroup (pairSubgroup first second)).map
      (pairSubgroup first second).subtype) (Component group) = {first, second} := by
  classical
  let image := (sylow : Subgroup (pairSubgroup first second)).map (pairSubgroup first second).subtype
  have first_fixed : first ∈ MulAction.fixedPoints image (Component group) := by
    apply MulAction.mem_fixedPoints.mpr
    intro element
    obtain ⟨original, _, image_eq⟩ := Subgroup.mem_map.mp element.property
    change element.val • first = first
    rw [← image_eq]
    exact original.property.1
  have second_fixed : second ∈ MulAction.fixedPoints image (Component group) := by
    apply MulAction.mem_fixedPoints.mpr
    intro element
    obtain ⟨original, _, image_eq⟩ := Subgroup.mem_map.mp element.property
    change element.val • second = second
    rw [← image_eq]
    exact original.property.2
  apply CFSG.OrderReductions.MaximalThreePoint.fixedPoints_le_two_eq_pair image first second distinct
    first_fixed second_fixed
  by_contra not_small
  have image_three : CFSG.OrderReductions.MaximalThreePoint.ThreePointPrime
      (points := Component group) prime image := ⟨sylow.isPGroup'.map _, by omega⟩
  obtain ⟨maximal_group, contains, maximal⟩ := Finite.exists_le_maximal image_three
  obtain ⟨base, base_fixed, base_even⟩ := even_point_rule maximal_group maximal
  have large_fixed : 2 < (MulAction.fixedPoints maximal_group (Component group)).ncard := by
    rw [← Nat.card_coe_set_eq]
    exact lt_of_lt_of_le (by decide : 2 < 3) maximal.prop.2
  obtain ⟨fixed_first, fixed_first_mem, fixed_second, fixed_second_mem, _, _,
    fixed_distinct, _, _⟩ := (Set.two_lt_ncard (Set.toFinite _)).mp large_fixed
  have regular := (CFSG.OrderReductions.LocalRegularity.maximal_uniform_regular_of_even_point prime
    maximal_group maximal first second distinct sylow contains base base_fixed base_even
    fixed_first fixed_second fixed_distinct fixed_first_mem fixed_second_mem).1
  exact no_regular fixed_first fixed_second fixed_distinct regular

theorem no_regular_double_transitive {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (even_point_rule : EvenPointRule (group := group) prime)
    (no_regular : NoRegularPair (group := group) prime)
    (degree : 3 ≤ Nat.card (Component group)) :
    MulAction.IsMultiplyPretransitive group (Component group) 2 := by
  apply CFSG.OrderReductions.FixedPairSylow.all_pairs_realization_two_pretransitive prime degree
  intro first second distinct
  obtain ⟨sylow⟩ := Sylow.nonempty (p := prime) (G := pairSubgroup first second)
  exact ⟨(sylow : Subgroup (pairSubgroup first second)).map (pairSubgroup first second).subtype,
    sylow.isPGroup'.map _, pair_sylow_fixed_pair_of_no_regular prime even_point_rule no_regular
      first second distinct sylow⟩

theorem no_regular_exists_fixed_pair {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (even_point_rule : EvenPointRule (group := group) prime)
    (no_regular : NoRegularPair (group := group) prime)
    (degree : 3 ≤ Nat.card (Component group)) :
    ∃ subgroup : Subgroup group, IsPGroup prime subgroup ∧
      Nat.card (MulAction.fixedPoints subgroup (Component group)) = 2 := by
  classical
  have degree_large : 2 < (Set.univ : Set (Component group)).ncard := by
    rw [Set.ncard_univ]
    omega
  obtain ⟨first, _, second, _, _, _, distinct, _, _⟩ :=
    (Set.two_lt_ncard (Set.toFinite _)).mp degree_large
  obtain ⟨sylow⟩ := Sylow.nonempty (p := prime) (G := pairSubgroup first second)
  refine ⟨(sylow : Subgroup (pairSubgroup first second)).map (pairSubgroup first second).subtype,
    sylow.isPGroup'.map _, ?_⟩
  rw [pair_sylow_fixed_pair_of_no_regular prime even_point_rule no_regular first second distinct sylow,
    Nat.card_coe_set_eq, Set.ncard_pair distinct]

@[expose] def sylowFixedPointsEquiv {group points : Type*} [Group group] [MulAction group points]
    (prime : ℕ) (sylow : Sylow prime group) (element : group) :
    MulAction.fixedPoints (sylow : Subgroup group) points ≃
      MulAction.fixedPoints ((element • sylow : Sylow prime group) : Subgroup group) points where
  toFun point := ⟨element • point.val,
    CFSG.OrderReductions.FixedPairSylow.sylow_smul_mem_fixedPoints prime sylow element point.property⟩
  invFun point := ⟨element⁻¹ • point.val, by
    have fixed := CFSG.OrderReductions.FixedPairSylow.sylow_smul_mem_fixedPoints prime
      (element • sylow) element⁻¹ point.property
    rw [inv_smul_smul] at fixed
    exact fixed⟩
  left_inv point := Subtype.ext (inv_smul_smul element point.val)
  right_inv point := Subtype.ext (smul_inv_smul element point.val)

theorem sylow_fixed_card_eq {group points : Type*} [Group group] [Finite group]
    [MulAction group points] (prime : ℕ) [Fact (Nat.Prime prime)]
    (first second : Sylow prime group) :
    Nat.card (MulAction.fixedPoints (first : Subgroup group) points) =
      Nat.card (MulAction.fixedPoints (second : Subgroup group) points) := by
  obtain ⟨element, equal_sylow⟩ := MulAction.exists_smul_eq group first second
  have card_equal := Nat.card_congr (sylowFixedPointsEquiv (points := points) prime first element)
  rwa [equal_sylow] at card_equal

theorem every_ambient_sylow_fixed_card_two {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (prime_odd : Odd prime)
    (subgroup : Subgroup group) (prime_group : IsPGroup prime subgroup)
    (fixed_two : Nat.card (MulAction.fixedPoints subgroup (Component group)) = 2)
    (sylow : Sylow prime group) :
    Nat.card (MulAction.fixedPoints (sylow : Subgroup group) (Component group)) = 2 := by
  have fixed_ncard : (MulAction.fixedPoints subgroup (Component group)).ncard = 2 := by
    rwa [Nat.card_coe_set_eq] at fixed_two
  obtain ⟨first, second, distinct, fixed_pair⟩ := Set.ncard_eq_two.mp fixed_ncard
  obtain ⟨ambient, _, ambient_fixed⟩ := CFSG.OrderReductions.FixedPairSylow.exists_ambient_sylow_fixed_pair_of_odd
    prime prime_odd subgroup prime_group first second distinct fixed_pair
  rw [← sylow_fixed_card_eq (points := Component group) prime ambient sylow, ambient_fixed,
    Nat.card_coe_set_eq, Set.ncard_pair distinct]

theorem no_regular_of_fixed_pair {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (prime_odd : Odd prime)
    (even_point_rule : EvenPointRule (group := group) prime)
    (subgroup : Subgroup group) (prime_group : IsPGroup prime subgroup)
    (fixed_two : Nat.card (MulAction.fixedPoints subgroup (Component group)) = 2) :
    NoRegularPair (group := group) prime := by
  classical
  intro first second distinct regular
  obtain ⟨initial⟩ := Sylow.nonempty (p := prime) (G := pairSubgroup first second)
  let image := (initial : Subgroup (pairSubgroup first second)).map (pairSubgroup first second).subtype
  have image_three : CFSG.OrderReductions.MaximalThreePoint.ThreePointPrime
      (points := Component group) prime image :=
    ⟨initial.isPGroup'.map _, pRegular_pair_sylow_three_fixed prime first second distinct regular initial⟩
  obtain ⟨maximal_group, initial_contains, maximal⟩ := Finite.exists_le_maximal image_three
  obtain ⟨base, base_fixed, base_even⟩ := even_point_rule maximal_group maximal
  obtain ⟨ambient, ambient_contains⟩ := maximal.prop.1.exists_le_sylow
  have ambient_card := every_ambient_sylow_fixed_card_two prime prime_odd subgroup prime_group
    fixed_two ambient
  have ambient_ncard : (MulAction.fixedPoints (ambient : Subgroup group) (Component group)).ncard = 2 := by
    rwa [Nat.card_coe_set_eq] at ambient_card
  obtain ⟨fixed_first, fixed_second, fixed_distinct, ambient_pair⟩ := Set.ncard_eq_two.mp ambient_ncard
  have first_fixed_ambient : fixed_first ∈ MulAction.fixedPoints (ambient : Subgroup group)
      (Component group) := by rw [ambient_pair]; exact Set.mem_insert _ _
  have second_fixed_ambient : fixed_second ∈ MulAction.fixedPoints (ambient : Subgroup group)
      (Component group) := by rw [ambient_pair]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have first_fixed := CFSG.OrderReductions.FixedPairSylow.fixedPoints_antitone ambient_contains first_fixed_ambient
  have second_fixed := CFSG.OrderReductions.FixedPairSylow.fixedPoints_antitone ambient_contains second_fixed_ambient
  obtain ⟨_, pair_sylow, pair_image⟩ := CFSG.OrderReductions.LocalRegularity.maximal_uniform_regular_of_even_point
    prime maximal_group maximal first second distinct initial initial_contains
    base base_fixed base_even fixed_first fixed_second fixed_distinct first_fixed second_fixed
  have ambient_le_pair : (ambient : Subgroup group) ≤ pairSubgroup fixed_first fixed_second := by
    intro element element_mem
    exact ⟨MulAction.mem_fixedPoints.mp first_fixed_ambient ⟨element, element_mem⟩,
      MulAction.mem_fixedPoints.mp second_fixed_ambient ⟨element, element_mem⟩⟩
  have internal_prime : IsPGroup prime
      ((ambient : Subgroup group).subgroupOf (pairSubgroup fixed_first fixed_second)) :=
    ambient.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe ambient_le_pair).symm
  have pair_le_internal : (pair_sylow : Subgroup (pairSubgroup fixed_first fixed_second)) ≤
      (ambient : Subgroup group).subgroupOf (pairSubgroup fixed_first fixed_second) := by
    intro element element_mem
    apply ambient_contains
    rw [← pair_image]
    exact Subgroup.mem_map_of_mem _ element_mem
  have internal_equal := pair_sylow.is_maximal' internal_prime pair_le_internal
  have ambient_equal : (ambient : Subgroup group) = maximal_group := by
    rw [← Subgroup.map_subgroupOf_eq_of_le ambient_le_pair, internal_equal, pair_image]
  rw [ambient_equal] at ambient_card
  have large := maximal.prop.2
  rw [ambient_card] at large
  omega

theorem no_regular_iff_fixed_pair {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (prime_odd : Odd prime)
    (even_point_rule : EvenPointRule (group := group) prime)
    (degree : 3 ≤ Nat.card (Component group)) :
    NoRegularPair (group := group) prime ↔
      ∃ subgroup : Subgroup group, IsPGroup prime subgroup ∧
        Nat.card (MulAction.fixedPoints subgroup (Component group)) = 2 := by
  constructor
  · exact fun no_regular => no_regular_exists_fixed_pair prime even_point_rule no_regular degree
  · rintro ⟨subgroup, prime_group, fixed_two⟩
    exact no_regular_of_fixed_pair prime prime_odd even_point_rule subgroup prime_group fixed_two

end CFSG.OrderReductions.EmptyRegularity
