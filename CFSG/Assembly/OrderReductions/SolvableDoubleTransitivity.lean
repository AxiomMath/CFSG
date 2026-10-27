module

public import CFSG.Assembly.OrderReductions.ContainedAuxiliary
public import CFSG.Assembly.OrderReductions.SolvableOddAuxiliary

public section

namespace CFSG.OrderReductions.SolvableDoubleTransitivity

universe group_universe

open CFSG.OrderReductions.InvolutionGraph CFSG.OrderReductions.TwoPointInvolutions CFSG.OrderReductions.PrimeRegular
open CFSG.OrderReductions.NormalizerAuxiliary CFSG.OrderReductions.PointMaximal CFSG.OrderReductions.MaximalThreePoint

theorem double_transitive_of_regular_pair
    {group : Type group_universe} [Group group] [Finite group]
    (induction_hypothesis : ∀ (smaller : Type group_universe) [Group smaller] [Finite smaller],
      Nat.card smaller < Nat.card group →
      ∀ first second : Involution smaller, first ≠ second → Commute first.val second.val →
        ∀ subgroup : Subgroup smaller, StronglyEmbedded subgroup →
          MulAction.IsMultiplyPretransitive smaller (CFSG.OrderReductions.StrongEmbedding.Conjugates subgroup) 2)
    (prime : ℕ) [Fact (Nat.Prime prime)] (odd_prime : Odd prime)
    (initial_first initial_second : Component group) (initial_distinct : initial_first ≠ initial_second)
    (regular : PRegular prime (pairSubgroup initial_first initial_second) (componentStabilizer initial_first))
    (prime_divides_involutions : prime ∣ Nat.card (Involution (componentStabilizer initial_first)))
    (four : ∀ point : Component group, ∃ first second : Involution group,
      first ≠ second ∧ Commute first.val second.val ∧
        first.val ∈ componentStabilizer point ∧ second.val ∈ componentStabilizer point)
    (odd_solvable : ∀ subgroup : Subgroup group, Odd (Nat.card subgroup) → Group.IsSolvable subgroup)
    (ambient_rule : ∀ other_prime : ℕ, Nat.Prime other_prime →
      CFSG.OrderReductions.EmptyRegularity.EvenPointRule (group := group) other_prime)
    (normalizer_rule : ∀ normal : Subgroup group, ∀ other_prime : ℕ, Nat.Prime other_prime →
      CFSG.OrderReductions.EmptyRegularity.EvenPointRule (group := Subgroup.normalizer (normal : Set group)) other_prime) :
    MulAction.IsMultiplyPretransitive group (Component group) 2 := by
  classical
  obtain ⟨initial_sylow⟩ := Sylow.nonempty (p := prime) (G := pairSubgroup initial_first initial_second)
  let initial_image := (initial_sylow : Subgroup (pairSubgroup initial_first initial_second)).map
    (pairSubgroup initial_first initial_second).subtype
  have initial_three : ThreePointPrime (points := Component group) prime initial_image :=
    ⟨initial_sylow.isPGroup'.map _, pRegular_pair_sylow_three_fixed prime initial_first initial_second
      initial_distinct regular initial_sylow⟩
  obtain ⟨subgroup, initial_contains, maximal⟩ := Finite.exists_le_maximal initial_three
  obtain ⟨point, point_fixed, point_even⟩ := ambient_rule prime (Fact.out : Nat.Prime prime) subgroup maximal
  obtain ⟨other, other_fixed, distinct_points⟩ : ∃ other : Component group,
      other ∈ MulAction.fixedPoints subgroup (Component group) ∧ point ≠ other := by
    by_contra none
    have all_equal : ∀ fixed : MulAction.fixedPoints subgroup (Component group), fixed = ⟨point, point_fixed⟩ := by
      intro fixed
      apply Subtype.ext
      by_contra unequal
      exact none ⟨fixed.val, fixed.property, Ne.symm unequal⟩
    have : Subsingleton (MulAction.fixedPoints subgroup (Component group)) :=
      ⟨fun first second => (all_equal first).trans (all_equal second).symm⟩
    have : Nonempty (MulAction.fixedPoints subgroup (Component group)) := ⟨⟨point, point_fixed⟩⟩
    have bound := Nat.card_unique (α := MulAction.fixedPoints subgroup (Component group))
    have lower := maximal.prop.2
    omega
  have degree : 3 ≤ Nat.card (Component group) := maximal.prop.2.trans
    (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective)
  have subgroup_contains : subgroup ≤ componentStabilizer point := by
    intro element membership
    exact MulAction.mem_fixedPoints.mp point_fixed ⟨element, membership⟩
  have point_maximal : Maximal (PointThreePointPrime prime point) subgroup := by
    refine ⟨⟨maximal.prop, subgroup_contains⟩, ?_⟩
    intro larger larger_prop contains
    exact maximal.2 larger_prop.1 contains
  have uniform := CFSG.OrderReductions.LocalRegularity.maximal_uniform_regular_of_even_point prime subgroup maximal
    initial_first initial_second initial_distinct initial_sylow initial_contains point point_fixed point_even
    point other distinct_points point_fixed other_fixed
  obtain ⟨sylow, sylow_image⟩ := uniform.2
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨inside_element, inside_order⟩ := exists_prime_orderOf_dvd_card' 2 point_even.two_dvd
  let inside : Involution group :=
    ⟨inside_element.val, (Subgroup.orderOf_coe inside_element).trans inside_order⟩
  have inside_mem : inside.val ∈ componentStabilizer point := inside_element.property.2
  have inside_normalizes : inside.val ∈ Subgroup.normalizer (subgroup : Set group) := inside_element.property.1
  have subgroup_odd : Odd (Nat.card subgroup) := by
    rw [← sylow_image, Subgroup.card_map_of_injective Subtype.val_injective, sylow.card_eq_multiplicity]
    exact odd_prime.pow
  have point_involution_nonempty : Nonempty (Involution (componentStabilizer point)) :=
    ⟨⟨⟨inside.val, inside_mem⟩, by rw [← Subgroup.orderOf_coe]; exact inside.property⟩⟩
  have point_card_eq := CFSG.OrderReductions.LocalRegularity.component_involution_card_eq initial_first point
  have point_divides : prime ∣ Nat.card (Involution (componentStabilizer point)) :=
    point_card_eq ▸ prime_divides_involutions
  have orbit_card : Nat.card (inversionSet subgroup inside) =
      CFSG.OrderReductions.PrimePart.primePart prime (Nat.card (Involution (componentStabilizer point))) := by
    rw [CFSG.OrderReductions.AuxiliaryMinimum.inversionSet_card_eq_orbit subgroup subgroup_odd inside inside_normalizes]
    have sylow_normalizes := inside_normalizes
    rw [← sylow_image] at sylow_normalizes
    have equal := invariant_pair_sylow_involution_orbit_card prime point other distinct_points sylow
      inside inside_mem sylow_normalizes
    rwa [sylow_image] at equal
  have inversion_large : 1 < Nat.card (inversionSet subgroup inside) := by
    rw [orbit_card, CFSG.OrderReductions.PrimePart.primePart]
    have positive := (Fact.out : Nat.Prime prime).factorization_pos_of_dvd
      (ne_of_gt (Nat.card_pos (α := Involution (componentStabilizer point)))) point_divides
    have lower := Nat.pow_le_pow_right (Fact.out : Nat.Prime prime).pos positive
    rw [pow_one] at lower
    exact (Fact.out : Nat.Prime prime).one_lt.trans_le lower
  have point_strong := componentStabilizer_stronglyEmbedded point ⟨other, distinct_points.symm⟩
  have noncentral : ¬ subgroup ≤ Subgroup.centralizer ({inside.val} : Set group) := by
    intro centralizes
    have all_one : inversionSet subgroup inside = {1} := by
      ext element
      constructor
      · intro membership
        have commutes := Subgroup.mem_centralizer_iff.mp (centralizes membership.1) inside.val (by simp)
        have fixed : (MulAut.conj inside.val) element = element := by
          rw [MulAut.conj_apply, commutes, mul_assoc, mul_inv_cancel, mul_one]
        have square_one : element ^ 2 = 1 := by
          rw [pow_two]
          calc
            element * element = element⁻¹ * element := by rw [membership.2.symm.trans fixed]
            _ = 1 := inv_mul_cancel element
        have odd_element := subgroup_odd.of_dvd_nat (subgroup.orderOf_dvd_natCard membership.1)
        have order_one : orderOf element = 1 := Nat.dvd_one.mp
          ((Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one square_one) (dvd_refl _)).trans
            (by rw [odd_element.coprime_two_left.gcd_eq_one]))
        exact Set.mem_singleton_iff.mpr (orderOf_eq_one_iff.mp order_one)
      · intro membership
        rw [Set.mem_singleton_iff.mp membership]
        exact ⟨subgroup.one_mem, by rw [map_one, inv_one]⟩
    rw [all_one, Nat.card_coe_set_eq, Set.ncard_singleton] at inversion_large
    omega
  have centralizer_solvable : ¬ Subgroup.centralizer (inversionSet subgroup inside) ≤ componentStabilizer point →
      Group.IsSolvable (Subgroup.centralizer (inversionSet subgroup inside)) := by
    intro crosses
    apply odd_solvable
    exact CFSG.OrderReductions.OutsideCentralizer.inversion_centralizer_odd (componentStabilizer point) point_strong subgroup
      subgroup_odd inside inside_mem inside_normalizes noncentral crosses
  obtain ⟨extension, auxiliary⟩ := CFSG.OrderReductions.ContainedAuxiliary.maximal_auxiliary_of_solvable_centralizer
    prime odd_prime (ambient_rule prime (Fact.out : Nat.Prime prime)) point point_strong subgroup point_maximal
    inside inside_mem inside_normalizes centralizer_solvable
  obtain ⟨outside, outside_mem, outside_not_mem, minimum⟩ :=
    CFSG.OrderReductions.AuxiliaryMinimum.exists_minimum_core_outside prime point (inversionSet subgroup inside)
      inside inside_mem extension auxiliary
  let outside_point := (commutingGraph group).connectedComponentMk outside
  have outside_distinct : point ≠ outside_point := by
    intro equal
    exact outside_not_mem ((componentStabilizer_involution_iff point outside).mpr equal.symm)
  have : Group.IsSolvable (pairSubgroup point outside_point) :=
    odd_solvable _ (distinct_componentStabilizers_odd_intersection point outside_point outside_distinct)
  have prime_divides_pair : prime ∣ Nat.card (pairSubgroup point outside_point) :=
    point_divides.trans (involution_card_dvd_pair_card point outside_point outside_distinct)
  obtain ⟨first, second, distinct_involutions, commutes, first_mem, second_mem⟩ := four point
  exact CFSG.OrderReductions.SolvableOddAuxiliary.double_transitive_of_minimum_solvable_pair induction_hypothesis
    prime point point_strong degree subgroup maximal.prop.1 subgroup_odd subgroup_contains inside inside_mem
    inside_normalizes orbit_card.ge extension auxiliary outside outside_mem outside_not_mem minimum prime_divides_pair
    first second distinct_involutions commutes first_mem second_mem ambient_rule
    (fun normal _ _ => normalizer_rule normal)

theorem double_transitive_inductive_step
    {group : Type group_universe} [Group group] [Finite group]
    (induction_hypothesis : ∀ (smaller : Type group_universe) [Group smaller] [Finite smaller],
      Nat.card smaller < Nat.card group →
      ∀ first second : Involution smaller, first ≠ second → Commute first.val second.val →
        ∀ subgroup : Subgroup smaller, StronglyEmbedded subgroup →
          MulAction.IsMultiplyPretransitive smaller (CFSG.OrderReductions.StrongEmbedding.Conjugates subgroup) 2)
    (point : Component group) (degree : 3 ≤ Nat.card (Component group))
    (four : ∀ point : Component group, ∃ first second : Involution group,
      first ≠ second ∧ Commute first.val second.val ∧
        first.val ∈ componentStabilizer point ∧ second.val ∈ componentStabilizer point)
    (odd_solvable : ∀ subgroup : Subgroup group, Odd (Nat.card subgroup) → Group.IsSolvable subgroup)
    (ambient_rule : ∀ other_prime : ℕ, Nat.Prime other_prime →
      CFSG.OrderReductions.EmptyRegularity.EvenPointRule (group := group) other_prime)
    (normalizer_rule : ∀ normal : Subgroup group, ∀ other_prime : ℕ, Nat.Prime other_prime →
      CFSG.OrderReductions.EmptyRegularity.EvenPointRule (group := Subgroup.normalizer (normal : Set group)) other_prime) :
    MulAction.IsMultiplyPretransitive group (Component group) 2 := by
  classical
  obtain ⟨other, distinct_points⟩ : ∃ other : Component group, point ≠ other := by
    by_contra none
    have : Subsingleton (Component group) := ⟨fun first second => by
      have first_eq : point = first := by by_contra unequal; exact none ⟨first, unequal⟩
      have second_eq : point = second := by by_contra unequal; exact none ⟨second, unequal⟩
      exact first_eq.symm.trans second_eq⟩
    have : Nonempty (Component group) := ⟨point⟩
    have card_one := Nat.card_unique (α := Component group)
    omega
  obtain ⟨first, second, distinct, commuting, first_mem, second_mem⟩ := four point
  let internal_first : Involution (componentStabilizer point) :=
    ⟨⟨first.val, first_mem⟩, by rw [← Subgroup.orderOf_coe]; exact first.property⟩
  let internal_second : Involution (componentStabilizer point) :=
    ⟨⟨second.val, second_mem⟩, by rw [← Subgroup.orderOf_coe]; exact second.property⟩
  have internal_distinct : internal_first ≠ internal_second := by
    intro equal
    exact distinct (Subtype.ext (congrArg (fun involution : Involution (componentStabilizer point) =>
      involution.val.val) equal))
  have internal_commuting : Commute internal_first.val internal_second.val := Subtype.ext commuting.eq
  obtain ⟨prime, prime_is_prime, odd_prime, divides, _⟩ := exists_odd_prime_dvd_pair_of_commuting
    point other distinct_points internal_first internal_second internal_distinct internal_commuting
  have : Fact (Nat.Prime prime) := ⟨prime_is_prime⟩
  by_cases no_regular : CFSG.OrderReductions.EmptyRegularity.NoRegularPair (group := group) prime
  · exact CFSG.OrderReductions.EmptyRegularity.no_regular_double_transitive prime (ambient_rule prime prime_is_prime)
      no_regular degree
  · have exists_regular : ∃ initial_first initial_second : Component group,
        initial_first ≠ initial_second ∧
          PRegular prime (pairSubgroup initial_first initial_second) (componentStabilizer initial_first) := by
      by_contra none
      apply no_regular
      intro initial_first initial_second initial_distinct regular
      exact none ⟨initial_first, initial_second, initial_distinct, regular⟩
    obtain ⟨initial_first, initial_second, initial_distinct, regular⟩ := exists_regular
    have initial_divides : prime ∣ Nat.card (Involution (componentStabilizer initial_first)) :=
      (CFSG.OrderReductions.LocalRegularity.component_involution_card_eq point initial_first) ▸ divides
    exact double_transitive_of_regular_pair induction_hypothesis prime odd_prime initial_first initial_second
      initial_distinct regular initial_divides four odd_solvable ambient_rule normalizer_rule

end CFSG.OrderReductions.SolvableDoubleTransitivity
