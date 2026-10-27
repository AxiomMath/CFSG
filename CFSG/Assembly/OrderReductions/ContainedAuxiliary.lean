module

public import CFSG.Assembly.OrderReductions.OutsideAuxiliary
public import CFSG.Assembly.OrderReductions.PointMaximalComplete

public section

namespace CFSG.OrderReductions.ContainedAuxiliary

open CFSG.OrderReductions.InvolutionGraph
open CFSG.OrderReductions.TwoPointInvolutions
open CFSG.OrderReductions.NormalizerAuxiliary

theorem maximal_contained_centralizer_auxiliary_of_no_fixed_two
    {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)]
    (even_point_rule : CFSG.OrderReductions.EmptyRegularity.EvenPointRule (group := group) prime)
    (point : Component group) (subgroup : Subgroup group)
    (maximal : Maximal (CFSG.OrderReductions.PointMaximal.PointThreePointPrime prime point) subgroup)
    (no_two : ∀ prime_subgroup : Subgroup group, IsPGroup prime prime_subgroup →
      Nat.card (MulAction.fixedPoints prime_subgroup (Component group)) ≠ 2)
    (inside : Involution group) (inside_mem : inside.val ∈ componentStabilizer point)
    (normalizes : inside.val ∈ Subgroup.normalizer (subgroup : Set group))
    (centralizer_le : Subgroup.centralizer (inversionSet subgroup inside) ≤ componentStabilizer point) :
    AuxiliaryData point (inversionSet subgroup inside) inside prime
      (Subgroup.normalizer (subgroup : Set group)) := by
  obtain ⟨global_maximal, other, distinct, sylow, image_eq⟩ :=
    CFSG.OrderReductions.PointMaximal.point_maximal_global_of_no_fixed_two prime point subgroup maximal no_two
  exact maximal_contained_centralizer_auxiliary prime even_point_rule subgroup global_maximal
    point other distinct sylow (image_eq ▸ le_rfl) point
    (MulAction.mem_fixedPoints.mpr fun element => maximal.prop.2 element.property)
    inside inside_mem normalizes centralizer_le

theorem maximal_auxiliary_of_regular_pair_and_solvable_centralizer
    {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (odd_prime : Odd prime)
    (even_point_rule : CFSG.OrderReductions.EmptyRegularity.EvenPointRule (group := group) prime)
    (point : Component group) (strong : StronglyEmbedded (componentStabilizer point))
    (subgroup : Subgroup group)
    (maximal : Maximal (CFSG.OrderReductions.PointMaximal.PointThreePointPrime prime point) subgroup)
    (first second : Component group) (distinct : first ≠ second)
    (regular : CFSG.OrderReductions.PrimeRegular.PRegular prime (pairSubgroup first second) (componentStabilizer first))
    (inside : Involution group) (inside_mem : inside.val ∈ componentStabilizer point)
    (normalizes : inside.val ∈ Subgroup.normalizer (subgroup : Set group))
    (centralizer_solvable : ¬ Subgroup.centralizer (inversionSet subgroup inside) ≤ componentStabilizer point →
      Group.IsSolvable (Subgroup.centralizer (inversionSet subgroup inside))) :
    ∃ extension : Subgroup group, AuxiliaryData point (inversionSet subgroup inside) inside prime extension := by
  classical
  by_cases centralizer_le : Subgroup.centralizer (inversionSet subgroup inside) ≤ componentStabilizer point
  · exact ⟨Subgroup.normalizer (subgroup : Set group),
      maximal_contained_centralizer_auxiliary_of_no_fixed_two prime even_point_rule point subgroup maximal
        (CFSG.OrderReductions.PointMaximal.no_fixed_two_of_regular prime odd_prime even_point_rule
          first second distinct regular) inside inside_mem normalizes centralizer_le⟩
  · have : Group.IsSolvable (Subgroup.centralizer (inversionSet subgroup inside)) :=
      centralizer_solvable centralizer_le
    exact CFSG.OrderReductions.OutsideAuxiliary.outside_centralizer_auxiliary_of_solvable prime point strong
      subgroup maximal.prop.1.1 maximal.prop.2 inside inside_mem normalizes centralizer_le

theorem maximal_contained_centralizer_auxiliary
    {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (odd_prime : Odd prime)
    (even_point_rule : CFSG.OrderReductions.EmptyRegularity.EvenPointRule (group := group) prime)
    (point : Component group) (subgroup : Subgroup group)
    (maximal : Maximal (CFSG.OrderReductions.PointMaximal.PointThreePointPrime prime point) subgroup)
    (inside : Involution group) (inside_mem : inside.val ∈ componentStabilizer point)
    (normalizes : inside.val ∈ Subgroup.normalizer (subgroup : Set group))
    (centralizer_le : Subgroup.centralizer (inversionSet subgroup inside) ≤ componentStabilizer point) :
    AuxiliaryData point (inversionSet subgroup inside) inside prime
      (Subgroup.normalizer (subgroup : Set group)) := by
  classical
  have global_maximal := (CFSG.OrderReductions.PointMaximalComplete.point_maximal_global_and_even
    prime odd_prime even_point_rule point subgroup maximal).1
  have fixed_large : 1 < (MulAction.fixedPoints subgroup (Component group)).ncard := by
    rw [← Nat.card_coe_set_eq]
    have := maximal.prop.1.2
    omega
  obtain ⟨first, first_fixed, second, second_fixed, distinct⟩ :=
    (Set.one_lt_ncard (Set.toFinite _)).mp fixed_large
  have other_exists : ∃ other ∈ MulAction.fixedPoints subgroup (Component group), point ≠ other := by
    by_cases first_eq : first = point
    · exact ⟨second, second_fixed, fun equal => distinct (first_eq.trans equal)⟩
    · exact ⟨first, first_fixed, Ne.symm first_eq⟩
  obtain ⟨other, other_fixed, other_distinct⟩ := other_exists
  have other_contains : subgroup ≤ componentStabilizer other :=
    fun element element_mem => MulAction.mem_fixedPoints.mp other_fixed ⟨element, element_mem⟩
  have other_maximal : Maximal (CFSG.OrderReductions.PointMaximal.PointThreePointPrime prime other) subgroup := by
    refine ⟨⟨global_maximal.prop, other_contains⟩, ?_⟩
    intro larger larger_prop contains
    exact global_maximal.2 larger_prop.1 contains
  have even_other := (CFSG.OrderReductions.PointMaximalComplete.point_maximal_global_and_even
    prime odd_prime even_point_rule other subgroup other_maximal).2
  exact normalizer_auxiliary_of_even_other prime point other other_distinct subgroup maximal.prop.1.1
    maximal.prop.2 inside inside_mem normalizes even_other centralizer_le

theorem maximal_auxiliary_of_solvable_centralizer
    {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (odd_prime : Odd prime)
    (even_point_rule : CFSG.OrderReductions.EmptyRegularity.EvenPointRule (group := group) prime)
    (point : Component group) (strong : StronglyEmbedded (componentStabilizer point))
    (subgroup : Subgroup group)
    (maximal : Maximal (CFSG.OrderReductions.PointMaximal.PointThreePointPrime prime point) subgroup)
    (inside : Involution group) (inside_mem : inside.val ∈ componentStabilizer point)
    (normalizes : inside.val ∈ Subgroup.normalizer (subgroup : Set group))
    (centralizer_solvable : ¬ Subgroup.centralizer (inversionSet subgroup inside) ≤ componentStabilizer point →
      Group.IsSolvable (Subgroup.centralizer (inversionSet subgroup inside))) :
    ∃ extension : Subgroup group, AuxiliaryData point (inversionSet subgroup inside) inside prime extension := by
  classical
  by_cases centralizer_le : Subgroup.centralizer (inversionSet subgroup inside) ≤ componentStabilizer point
  · exact ⟨Subgroup.normalizer (subgroup : Set group), maximal_contained_centralizer_auxiliary
      prime odd_prime even_point_rule point subgroup maximal inside inside_mem normalizes centralizer_le⟩
  · have : Group.IsSolvable (Subgroup.centralizer (inversionSet subgroup inside)) :=
      centralizer_solvable centralizer_le
    exact CFSG.OrderReductions.OutsideAuxiliary.outside_centralizer_auxiliary_of_solvable prime point strong
      subgroup maximal.prop.1.1 maximal.prop.2 inside inside_mem normalizes centralizer_le

end CFSG.OrderReductions.ContainedAuxiliary
