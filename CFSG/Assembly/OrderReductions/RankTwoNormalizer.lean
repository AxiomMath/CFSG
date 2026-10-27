module

public import CFSG.Assembly.OrderReductions.RankTwoContainment
public import CFSG.Assembly.OrderReductions.PrimeRegular

public section

namespace CFSG.OrderReductions.RankTwoNormalizer

open CFSG.OrderReductions.InvolutionGraph

theorem pair_point_normalizer_odd {group : Type*} [Group group] [Finite group]
    (first second : Component group) (distinct_points : first ≠ second)
    (first_involution second_involution : Involution group)
    (distinct_involutions : first_involution ≠ second_involution)
    (commutes : Commute first_involution.val second_involution.val)
    (first_mem : first_involution.val ∈ componentStabilizer first)
    (second_mem : second_involution.val ∈ componentStabilizer first) :
    Odd (Nat.card ↥(Subgroup.normalizer
      (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second : Set group) ⊓ componentStabilizer first)) := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  by_contra not_odd
  obtain ⟨element, element_order⟩ := exists_prime_orderOf_dvd_card' 2
    (Nat.not_odd_iff_even.mp not_odd).two_dvd
  let inside : Involution group :=
    ⟨element.val, (Subgroup.orderOf_coe element).trans element_order⟩
  let pair := CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second
  let overgroup := pair ⊔ Subgroup.zpowers inside.val
  have inside_mem : inside.val ∈ componentStabilizer first := element.property.2
  have normalizes : inside.val ∈ Subgroup.normalizer (pair : Set group) := element.property.1
  have cyclic_normalizes : Subgroup.zpowers inside.val ≤ Subgroup.normalizer (pair : Set group) :=
    Subgroup.zpowers_le.mpr normalizes
  have : (pair.subgroupOf overgroup).Normal := by
    change (pair.subgroupOf (pair ⊔ Subgroup.zpowers inside.val)).Normal
    rw [sup_comm]
    exact Subgroup.normal_subgroupOf_sup_of_le_normalizer cyclic_normalizes
  have inside_overgroup : inside.val ∈ overgroup :=
    (show Subgroup.zpowers inside.val ≤ overgroup from le_sup_right) (Subgroup.mem_zpowers _)
  let internal_inside : overgroup := ⟨inside.val, inside_overgroup⟩
  let projection := QuotientGroup.mk' (pair.subgroupOf overgroup)
  have image_square : projection internal_inside * projection internal_inside = 1 := by
    rw [← map_mul]
    have square : internal_inside * internal_inside = 1 :=
      Subtype.ext (CFSG.OrderReductions.InvolutionFusion.involution_mul_self inside)
    rw [square, map_one]
  have common_image (involution : Involution group) (mem_first : involution.val ∈ componentStabilizer first) :
      ∃ internal : overgroup, internal.val = involution.val ∧ projection internal = projection internal_inside := by
    obtain ⟨conjugator, conjugates⟩ := CFSG.OrderReductions.PrimeRegular.pair_conjugates_involutions
      first second distinct_points inside involution inside_mem mem_first
    have internal_mem : involution.val ∈ overgroup := by
      have conjugate_mem := overgroup.mul_mem
        (overgroup.mul_mem ((show pair ≤ overgroup from le_sup_left) conjugator.property) inside_overgroup)
        (overgroup.inv_mem ((show pair ≤ overgroup from le_sup_left) conjugator.property))
      have equal_values : conjugator.val * inside.val * conjugator.val⁻¹ = involution.val :=
        congrArg Subtype.val conjugates
      exact equal_values ▸ conjugate_mem
    let internal : overgroup := ⟨involution.val, internal_mem⟩
    let internal_conjugator : overgroup := ⟨conjugator.val, (show pair ≤ overgroup from le_sup_left) conjugator.property⟩
    have conjugator_kernel : projection internal_conjugator = 1 :=
      (QuotientGroup.eq_one_iff internal_conjugator).mpr conjugator.property
    have internal_eq : internal = internal_conjugator * internal_inside * internal_conjugator⁻¹ := by
      apply Subtype.ext
      exact (congrArg Subtype.val conjugates).symm
    refine ⟨internal, rfl, ?_⟩
    rw [internal_eq, map_mul, map_mul, map_inv, conjugator_kernel, one_mul, inv_one, mul_one]
  obtain ⟨internal_first, first_eq, first_image⟩ := common_image first_involution first_mem
  obtain ⟨internal_second, second_eq, second_image⟩ := common_image second_involution second_mem
  have product_image : projection (internal_first * internal_second) = 1 := by
    rw [map_mul, first_image, second_image]
    exact image_square
  have product_mem : first_involution.val * second_involution.val ∈ pair := by
    have internal_mem := (QuotientGroup.eq_one_iff (internal_first * internal_second)).mp product_image
    change internal_first.val * internal_second.val ∈ pair at internal_mem
    rwa [first_eq, second_eq] at internal_mem
  have product_order := CFSG.OrderReductions.RankTwoContainment.commuting_involution_product
    first_involution second_involution distinct_involutions commutes
  have divides := pair.orderOf_dvd_natCard product_mem
  rw [product_order] at divides
  exact (distinct_componentStabilizers_odd_intersection first second distinct_points).not_two_dvd_nat divides

theorem pair_invariant_of_every_prime_regular {group : Type*} [Group group] [Finite group]
    (first second : Component group) (distinct : first ≠ second)
    (involution : Involution group) (mem_first : involution.val ∈ componentStabilizer first)
    (all_regular : ∀ prime : ℕ, Nat.Prime prime →
      prime ∣ Nat.card (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second) →
        CFSG.OrderReductions.PrimeRegular.PRegular prime (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second)
          (componentStabilizer first)) :
    involution.val ∈ Subgroup.normalizer (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second : Set group) := by
  let pair := CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second
  let common := CFSG.OrderReductions.InvolutiveIntersection.intersection (MulAut.conj involution.val) pair
  have contains : common ≤ pair := inf_le_left
  have full : common.subgroupOf pair = ⊤ := by
    apply CFSG.OrderReductions.PrimePart.eq_top_of_contains_sylow_for_every_prime
    intro prime prime_is_prime
    have : Fact (Nat.Prime prime) := ⟨prime_is_prime⟩
    by_cases divides : prime ∣ Nat.card pair
    · obtain ⟨sylow, normalizes⟩ := CFSG.OrderReductions.PrimeRegular.pRegular_pair_every_involution_invariant_sylow
        prime first second distinct (all_regular prime prime_is_prime divides) involution mem_first
      have invariant : ((sylow : Subgroup pair).map pair.subtype).map
          (MulAut.conj involution.val).toMonoidHom = (sylow : Subgroup pair).map pair.subtype :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp normalizes
      have image_pair : (sylow : Subgroup pair).map pair.subtype ≤ pair := Subgroup.map_subtype_le _
      have image_common := CFSG.OrderReductions.InvolutiveIntersection.invariant_le_intersection
        (MulAut.conj involution.val) pair _ image_pair invariant
      refine ⟨sylow, ?_⟩
      intro element element_mem
      exact image_common (Subgroup.mem_map_of_mem pair.subtype element_mem)
    · obtain ⟨sylow⟩ := Sylow.nonempty (p := prime) (G := pair)
      have sylow_card : Nat.card (sylow : Subgroup pair) = 1 := by
        rw [sylow.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd divides, pow_zero]
      refine ⟨sylow, ?_⟩
      rw [Subgroup.card_eq_one.mp sylow_card]
      exact bot_le
  have common_eq : common = pair :=
    le_antisymm contains (Subgroup.subgroupOf_eq_top.mp full)
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  have common_invariant := CFSG.OrderReductions.InvolutiveIntersection.intersection_invariant
    (MulAut.conj involution.val) (CFSG.OrderReductions.PrimeRegular.involution_conjugation_involutive involution) pair
  change common.map (MulAut.conj involution.val).toMonoidHom = common at common_invariant
  rwa [common_eq] at common_invariant

theorem exists_nonregular_prime {group : Type*} [Group group] [Finite group]
    (first second : Component group) (distinct_points : first ≠ second)
    (first_involution second_involution : Involution group)
    (distinct_involutions : first_involution ≠ second_involution)
    (commutes : Commute first_involution.val second_involution.val)
    (first_mem : first_involution.val ∈ componentStabilizer first)
    (second_mem : second_involution.val ∈ componentStabilizer first) :
    ∃ prime : ℕ, Nat.Prime prime ∧ Odd prime ∧
      prime ∣ Nat.card (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second) ∧
        ¬ CFSG.OrderReductions.PrimeRegular.PRegular prime (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second)
          (componentStabilizer first) := by
  classical
  have odd_pair := distinct_componentStabilizers_odd_intersection first second distinct_points
  have exists_prime : ∃ prime : ℕ, Nat.Prime prime ∧
      prime ∣ Nat.card (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second) ∧
        ¬ CFSG.OrderReductions.PrimeRegular.PRegular prime (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second)
          (componentStabilizer first) := by
    by_contra no_prime
    push Not at no_prime
    have normalizes := pair_invariant_of_every_prime_regular first second distinct_points first_involution
      first_mem no_prime
    have odd_normalizer := pair_point_normalizer_odd first second distinct_points
      first_involution second_involution distinct_involutions commutes first_mem second_mem
    have divides := Subgroup.orderOf_dvd_natCard
      (Subgroup.normalizer (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second : Set group) ⊓
        componentStabilizer first) ⟨normalizes, first_mem⟩
    rw [first_involution.property] at divides
    exact odd_normalizer.not_two_dvd_nat divides
  obtain ⟨prime, prime_is_prime, divides, not_regular⟩ := exists_prime
  refine ⟨prime, prime_is_prime, prime_is_prime.odd_of_ne_two ?_, divides, not_regular⟩
  intro equal_two
  exact odd_pair.not_two_dvd_nat (equal_two ▸ divides)

end CFSG.OrderReductions.RankTwoNormalizer
