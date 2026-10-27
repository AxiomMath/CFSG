module

public import CFSG.Assembly.OrderReductions.AuxiliaryMinimum

public section

namespace CFSG.OrderReductions.DoubleTransitiveSylow

open CFSG.OrderReductions.InvolutionGraph
open CFSG.OrderReductions.TwoPointInvolutions
open CFSG.OrderReductions.PrimeRegular

theorem pRegular_pair_transport {group : Type*} [Group group] [Finite group]
    (prime : ℕ) (two_transitive : MulAction.IsMultiplyPretransitive group (Component group) 2)
    (first second third fourth : Component group) (first_distinct : first ≠ second)
    (third_distinct : third ≠ fourth)
    (regular : PRegular prime (pairSubgroup first second) (componentStabilizer first)) :
    PRegular prime (pairSubgroup third fourth) (componentStabilizer third) := by
  obtain ⟨acting, first_moves, second_moves⟩ :=
    MulAction.is_two_pretransitive_iff.mp two_transitive first_distinct third_distinct
  have pair_image : (pairSubgroup first second).map (MulAut.conj acting).toMonoidHom =
      pairSubgroup third fourth := by
    rw [pairSubgroup, Subgroup.map_inf _ _ _ (MulAut.conj acting).injective,
      ← componentStabilizer_smul, ← componentStabilizer_smul, first_moves, second_moves]
    rfl
  have transported := CFSG.OrderReductions.AuxiliaryMinimum.pRegular_map_equiv prime (MulAut.conj acting)
    (pairSubgroup first second) (componentStabilizer first) regular
  rwa [pair_image, ← componentStabilizer_smul, first_moves] at transported

theorem no_regular_of_odd_sylow_normalizer {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)]
    (two_transitive : MulAction.IsMultiplyPretransitive group (Component group) 2)
    (first second : Component group) (distinct : first ≠ second)
    (sylow : Sylow prime (pairSubgroup first second))
    (odd_normalizer : Odd (Nat.card ↥(Subgroup.normalizer
      ((sylow : Subgroup (pairSubgroup first second)).map (pairSubgroup first second).subtype : Set group) ⊓
        componentStabilizer first))) : CFSG.OrderReductions.EmptyRegularity.NoRegularPair (group := group) prime := by
  intro third fourth other_distinct regular
  have regular_first := pRegular_pair_transport prime two_transitive third fourth first second
    other_distinct distinct regular
  have even_normalizer := (pRegular_iff_every_even_normalizer prime (pairSubgroup first second)
    (componentStabilizer first) inf_le_left
    (distinct_componentStabilizers_odd_intersection first second distinct)).mp regular_first sylow
  exact odd_normalizer.not_two_dvd_nat even_normalizer.two_dvd

theorem fixed_pair_of_odd_sylow_normalizer {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)]
    (even_point_rule : CFSG.OrderReductions.EmptyRegularity.EvenPointRule (group := group) prime)
    (two_transitive : MulAction.IsMultiplyPretransitive group (Component group) 2)
    (first second : Component group) (distinct : first ≠ second)
    (sylow : Sylow prime (pairSubgroup first second))
    (odd_normalizer : Odd (Nat.card ↥(Subgroup.normalizer
      ((sylow : Subgroup (pairSubgroup first second)).map (pairSubgroup first second).subtype : Set group) ⊓
        componentStabilizer first))) :
    MulAction.fixedPoints ((sylow : Subgroup (pairSubgroup first second)).map
      (pairSubgroup first second).subtype) (Component group) = {first, second} := by
  exact CFSG.OrderReductions.EmptyRegularity.pair_sylow_fixed_pair_of_no_regular prime even_point_rule
    (no_regular_of_odd_sylow_normalizer prime two_transitive first second distinct sylow odd_normalizer)
    first second distinct sylow

theorem ambient_sylow_of_odd_sylow_normalizer {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (odd_prime : Odd prime)
    (even_point_rule : CFSG.OrderReductions.EmptyRegularity.EvenPointRule (group := group) prime)
    (two_transitive : MulAction.IsMultiplyPretransitive group (Component group) 2)
    (first second : Component group) (distinct : first ≠ second)
    (sylow : Sylow prime (pairSubgroup first second))
    (odd_normalizer : Odd (Nat.card ↥(Subgroup.normalizer
      ((sylow : Subgroup (pairSubgroup first second)).map (pairSubgroup first second).subtype : Set group) ⊓
        componentStabilizer first))) :
    ∃ ambient : Sylow prime group, (ambient : Subgroup group) =
      (sylow : Subgroup (pairSubgroup first second)).map (pairSubgroup first second).subtype := by
  let image := (sylow : Subgroup (pairSubgroup first second)).map (pairSubgroup first second).subtype
  have fixed_pair := fixed_pair_of_odd_sylow_normalizer prime even_point_rule two_transitive
    first second distinct sylow odd_normalizer
  obtain ⟨ambient, contains, ambient_fixed⟩ := CFSG.OrderReductions.FixedPairSylow.exists_ambient_sylow_fixed_pair_of_odd
    prime odd_prime image (sylow.isPGroup'.map _) first second distinct fixed_pair
  have ambient_pair : (ambient : Subgroup group) ≤ pairSubgroup first second := by
    intro element element_mem
    have first_fixed : first ∈ MulAction.fixedPoints (ambient : Subgroup group) (Component group) := by
      rw [ambient_fixed]
      exact Set.mem_insert _ _
    have second_fixed : second ∈ MulAction.fixedPoints (ambient : Subgroup group) (Component group) := by
      rw [ambient_fixed]
      exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    exact ⟨MulAction.mem_fixedPoints.mp first_fixed ⟨element, element_mem⟩,
      MulAction.mem_fixedPoints.mp second_fixed ⟨element, element_mem⟩⟩
  have internal_prime : IsPGroup prime ((ambient : Subgroup group).subgroupOf (pairSubgroup first second)) :=
    ambient.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe ambient_pair).symm
  have internal_contains : (sylow : Subgroup (pairSubgroup first second)) ≤
      (ambient : Subgroup group).subgroupOf (pairSubgroup first second) := by
    intro element element_mem
    exact contains (Subgroup.mem_map_of_mem _ element_mem)
  have equal_internal := sylow.is_maximal' internal_prime internal_contains
  refine ⟨ambient, ?_⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le ambient_pair, equal_internal]

end CFSG.OrderReductions.DoubleTransitiveSylow
