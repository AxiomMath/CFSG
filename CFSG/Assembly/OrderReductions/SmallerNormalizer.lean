module

public import CFSG.Assembly.OrderReductions.NormalizerQuotient
public import CFSG.Assembly.OrderReductions.InternalComponents

public section

namespace CFSG.OrderReductions.SmallerNormalizer

universe group_universe

open CFSG.OrderReductions.InvolutionGraph

theorem two_transitive_of_smaller_quotient
    {group : Type group_universe} [Group group] [Finite group]
    (induction_hypothesis : ∀ (smaller : Type group_universe) [Group smaller] [Finite smaller],
      Nat.card smaller < Nat.card group →
      ∀ first second : Involution smaller, first ≠ second → Commute first.val second.val →
        ∀ subgroup : Subgroup smaller, StronglyEmbedded subgroup →
          MulAction.IsMultiplyPretransitive smaller (CFSG.OrderReductions.StrongEmbedding.Conjugates subgroup) 2)
    (point other : Component group) (distinct_points : point ≠ other)
    (strong : StronglyEmbedded (componentStabilizer point))
    (normal : Subgroup group) (nontrivial : normal ≠ ⊥)
    (contains : normal ≤ CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup point other)
    [(normal.subgroupOf (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup point other)).Normal]
    (inside outside : Involution group) (inside_mem : inside.val ∈ componentStabilizer point)
    (outside_not_mem : outside.val ∉ componentStabilizer point)
    (inside_normalizes : inside.val ∈ Subgroup.normalizer (normal : Set group))
    (outside_normalizes : outside.val ∈ Subgroup.normalizer (normal : Set group))
    (first second : Involution group) (distinct_involutions : first ≠ second)
    (commutes : Commute first.val second.val)
    (first_mem : first.val ∈ componentStabilizer point)
    (second_mem : second.val ∈ componentStabilizer point) :
    MulAction.IsMultiplyPretransitive (Subgroup.normalizer (normal : Set group))
      (Component (Subgroup.normalizer (normal : Set group))) 2 := by
  let normalizer := Subgroup.normalizer (normal : Set group)
  let kernel := normal.subgroupOf normalizer
  let intersection := (componentStabilizer point).subgroupOf normalizer
  have all_normalize := CFSG.OrderReductions.NormalizerQuotient.all_point_involutions_normalize
    point other distinct_points normal contains inside inside_mem inside_normalizes
  have first_normalizes := all_normalize first first_mem
  have second_normalizes := all_normalize second second_mem
  let internal_inside : Involution normalizer :=
    ⟨⟨inside.val, inside_normalizes⟩, by rw [← Subgroup.orderOf_coe]; exact inside.property⟩
  let internal_first : Involution normalizer :=
    ⟨⟨first.val, first_normalizes⟩, by rw [← Subgroup.orderOf_coe]; exact first.property⟩
  let internal_second : Involution normalizer :=
    ⟨⟨second.val, second_normalizes⟩, by rw [← Subgroup.orderOf_coe]; exact second.property⟩
  have internal_distinct : internal_first ≠ internal_second := by
    intro equal
    exact distinct_involutions (Subtype.ext (congrArg (fun involution : Involution normalizer => involution.val.val) equal))
  have internal_commutes : Commute internal_first.val internal_second.val := Subtype.ext commutes.eq
  have strong_internal := CFSG.OrderReductions.NormalizerQuotient.normalizer_intersection_strong point strong normal
    inside outside inside_mem outside_not_mem inside_normalizes outside_normalizes
  have odd_normal : Odd (Nat.card normal) :=
    (distinct_componentStabilizers_odd_intersection point other distinct_points).of_dvd_nat
      (Subgroup.card_dvd_of_le contains)
  have odd_kernel_group : Odd (Nat.card kernel) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe normal.le_normalizer).toEquiv]
    exact odd_normal
  let projection := QuotientGroup.mk' kernel
  have odd_kernel : Odd (Nat.card projection.ker) := by
    rwa [QuotientGroup.ker_mk']
  have kernel_le : projection.ker ≤ intersection := by
    rw [QuotientGroup.ker_mk']
    intro element element_mem
    exact (contains element_mem).1
  have quotient_strong := CFSG.OrderReductions.StrongEmbeddingInheritance.surjective_odd_kernel_stronglyEmbedded
    projection (QuotientGroup.mk'_surjective kernel) intersection strong_internal kernel_le odd_kernel
  obtain ⟨first_image, second_image, _, _, image_distinct, image_commutes⟩ :=
    CFSG.OrderReductions.NormalizerQuotient.commuting_pair_survives_odd_kernel projection odd_kernel
      internal_first internal_second internal_distinct internal_commutes
  have quotient_transitive := induction_hypothesis (normalizer ⧸ kernel)
    (CFSG.OrderReductions.NormalizerQuotient.normalizer_quotient_card_lt normal nontrivial)
    first_image second_image image_distinct image_commutes (intersection.map projection) quotient_strong
  have conjugates_transitive := (CFSG.OrderReductions.StrongEmbeddingInheritance.conjugates_two_pretransitive_iff
    projection (QuotientGroup.mk'_surjective kernel) intersection kernel_le).mpr quotient_transitive
  have intersection_eq := CFSG.OrderReductions.InternalComponents.stabilizer_intersection_eq_internal
    point strong normalizer all_normalize internal_inside inside_mem
  change intersection = componentStabilizer ((commutingGraph normalizer).connectedComponentMk internal_inside) at intersection_eq
  rw [intersection_eq] at conjugates_transitive
  exact (CFSG.OrderReductions.InternalComponents.components_two_transitive_iff_conjugates
    ((commutingGraph normalizer).connectedComponentMk internal_inside)).mpr conjugates_transitive

end CFSG.OrderReductions.SmallerNormalizer
