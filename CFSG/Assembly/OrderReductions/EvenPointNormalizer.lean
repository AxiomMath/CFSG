module

public import CFSG.Assembly.OrderReductions.RankTwoContainment
public import CFSG.Assembly.OrderReductions.OddKernelInvolutions
public import CFSG.Assembly.OrderReductions.MaximalThreePoint

public section

namespace CFSG.OrderReductions.EvenPointNormalizer

open CFSG.OrderReductions.InvolutionGraph
open CFSG.OrderReductions.TwoPointInvolutions

theorem exists_even_point_normalizer_of_four_involutions {group : Type*}
    [Group group] [Finite group] (subgroup : Subgroup group)
    (odd_subgroup : Odd (Nat.card subgroup))
    (even_normalizer : Even (Nat.card (Subgroup.normalizer (subgroup : Set group))))
    (first second : Involution (Subgroup.normalizer (subgroup : Set group)))
    (distinct : first ≠ second) (commutes : Commute first.val second.val) :
    ∃ point ∈ MulAction.fixedPoints subgroup (Component group),
      Even (Nat.card ↥(Subgroup.normalizer (subgroup : Set group) ⊓ componentStabilizer point)) := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  let normalizer := Subgroup.normalizer (subgroup : Set group)
  obtain ⟨element, element_order⟩ := exists_prime_orderOf_dvd_card' 2 even_normalizer.two_dvd
  let involution : Involution group :=
    ⟨element.val, by rw [Subgroup.orderOf_coe]; exact element_order⟩
  let point := (commutingGraph group).connectedComponentMk involution
  have involution_mem : involution.val ∈ componentStabilizer point :=
    involution_mem_componentStabilizer involution
  have subgroup_le : subgroup ≤ componentStabilizer point := by
    by_cases other : ∃ different : Component group, different ≠ point
    · exact CFSG.OrderReductions.RankTwoContainment.odd_subgroup_le_of_four_involutions_in_normalizer
        (componentStabilizer point) (componentStabilizer_stronglyEmbedded point other)
        subgroup odd_subgroup first second distinct commutes involution element.property involution_mem
    · intro current current_mem
      change current • point = point
      by_contra moves
      exact other ⟨current • point, moves⟩
  refine ⟨point, ?_, ?_⟩
  · apply MulAction.mem_fixedPoints.mpr
    intro current
    exact subgroup_le current.property
  · have divides := Subgroup.orderOf_dvd_natCard (normalizer ⊓ componentStabilizer point)
      (show involution.val ∈ normalizer ⊓ componentStabilizer point from
        ⟨element.property, involution_mem⟩)
    rw [involution.property] at divides
    exact even_iff_two_dvd.mpr divides

theorem maximal_exists_even_point_normalizer_of_four_involutions {group : Type*}
    [Group group] [Finite group] (prime : ℕ) [Fact (Nat.Prime prime)]
    (prime_odd : Odd prime) (subgroup : Subgroup group)
    (maximal : Maximal
      (CFSG.OrderReductions.MaximalThreePoint.ThreePointPrime (points := Component group) prime) subgroup)
    (first second : Involution (Subgroup.normalizer (subgroup : Set group)))
    (distinct : first ≠ second) (commutes : Commute first.val second.val) :
    ∃ point ∈ MulAction.fixedPoints subgroup (Component group),
      Even (Nat.card ↥(Subgroup.normalizer (subgroup : Set group) ⊓ componentStabilizer point)) := by
  obtain ⟨exponent, order_eq⟩ := IsPGroup.iff_card.mp maximal.prop.1
  have odd_subgroup : Odd (Nat.card subgroup) := by
    rw [order_eq]
    exact prime_odd.pow
  exact exists_even_point_normalizer_of_four_involutions subgroup odd_subgroup
    (CFSG.OrderReductions.MaximalThreePoint.maximal_normalizer_even prime subgroup maximal)
    first second distinct commutes

theorem odd_prime_small_orbit_fixed {actor points : Type*} [Group actor]
    [MulAction actor points] [Finite points] (prime : ℕ) [Fact (Nat.Prime prime)]
    (prime_odd : Odd prime) (prime_actor : IsPGroup prime actor) (point : points)
    (small : Nat.card (MulAction.orbit actor point) ≤ 2) :
    point ∈ MulAction.fixedPoints actor points := by
  obtain ⟨exponent, orbit_card⟩ := prime_actor.card_orbit point
  have odd_orbit : Odd (Nat.card (MulAction.orbit actor point)) := by
    rw [orbit_card]
    exact prime_odd.pow
  have positive : 0 < Nat.card (MulAction.orbit actor point) := by
    have : Nonempty (MulAction.orbit actor point) := ⟨⟨point, MulAction.mem_orbit_self point⟩⟩
    exact Nat.card_pos
  have orbit_one : Nat.card (MulAction.orbit actor point) = 1 := by
    obtain ⟨half, odd_eq⟩ := odd_orbit
    omega
  have := (Nat.card_eq_one_iff_unique.mp orbit_one).1
  apply MulAction.mem_fixedPoints.mpr
  intro acting
  have equal_points : (⟨acting • point, MulAction.mem_orbit_iff.mpr ⟨acting, rfl⟩⟩ :
      MulAction.orbit actor point) = ⟨point, MulAction.mem_orbit_self point⟩ := Subsingleton.elim _ _
  exact congrArg Subtype.val equal_points

theorem subgroup_orbit_subset_of_le {group points : Type*} [Group group]
    [MulAction group points] (smaller larger : Subgroup group) (contains : smaller ≤ larger)
    (point : points) : MulAction.orbit smaller point ⊆ MulAction.orbit larger point := by
  intro moved mem_orbit
  obtain ⟨acting, acting_eq⟩ := MulAction.mem_orbit_iff.mp mem_orbit
  exact MulAction.mem_orbit_iff.mpr ⟨⟨acting.val, contains acting.property⟩, acting_eq⟩

theorem normalizer_orbit_subset_fixed {group points : Type*} [Group group]
    [MulAction group points] (subgroup : Subgroup group) (point : points)
    (fixed : point ∈ MulAction.fixedPoints subgroup points) :
    MulAction.orbit (Subgroup.normalizer (subgroup : Set group)) point ⊆
      MulAction.fixedPoints subgroup points := by
  intro moved mem_orbit
  obtain ⟨acting, acting_eq⟩ := MulAction.mem_orbit_iff.mp mem_orbit
  rw [← acting_eq]
  exact CFSG.OrderReductions.FixedPairSylow.normalizer_preserves_fixedPoints subgroup acting.val
    acting.property fixed

theorem even_point_normalizer_of_singleton_orbit {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group)
    (even_normalizer : Even (Nat.card (Subgroup.normalizer (subgroup : Set group))))
    (point : Component group)
    (singleton : Nat.card (MulAction.orbit (Subgroup.normalizer (subgroup : Set group)) point) = 1) :
    Even (Nat.card ↥(Subgroup.normalizer (subgroup : Set group) ⊓ componentStabilizer point)) := by
  have := (Nat.card_eq_one_iff_unique.mp singleton).1
  have normalizer_le : Subgroup.normalizer (subgroup : Set group) ≤ componentStabilizer point := by
    intro acting normalizes
    have equal_points : (⟨acting • point,
        MulAction.mem_orbit_iff.mpr ⟨⟨acting, normalizes⟩, rfl⟩⟩ :
        MulAction.orbit (Subgroup.normalizer (subgroup : Set group)) point) =
        ⟨point, MulAction.mem_orbit_self point⟩ := Subsingleton.elim _ _
    exact congrArg Subtype.val equal_points
  rwa [inf_eq_left.mpr normalizer_le]

theorem maximal_large_orbit_or_even_point_normalizer {group : Type*}
    [Group group] [Finite group] (prime : ℕ) [Fact (Nat.Prime prime)]
    (prime_odd : Odd prime) (subgroup : Subgroup group)
    (maximal : Maximal
      (CFSG.OrderReductions.MaximalThreePoint.ThreePointPrime (points := Component group) prime) subgroup) :
    (∃ point ∈ MulAction.fixedPoints subgroup (Component group),
      Even (Nat.card ↥(Subgroup.normalizer (subgroup : Set group) ⊓ componentStabilizer point))) ∨
    ∃ point ∈ MulAction.fixedPoints subgroup (Component group),
      3 ≤ Nat.card (MulAction.orbit (Subgroup.normalizer (subgroup : Set group)) point) := by
  classical
  let normalizer := Subgroup.normalizer (subgroup : Set group)
  have normalizer_even := CFSG.OrderReductions.MaximalThreePoint.maximal_normalizer_even prime subgroup maximal
  by_cases even_point : ∃ point ∈ MulAction.fixedPoints subgroup (Component group),
      Even (Nat.card ↥(normalizer ⊓ componentStabilizer point))
  · exact Or.inl even_point
  · apply Or.inr
    by_contra no_large_orbit
    push Not at no_large_orbit
    have orbit_small : ∀ point ∈ MulAction.fixedPoints subgroup (Component group),
        Nat.card (MulAction.orbit normalizer point) ≤ 2 := by
      intro point fixed
      have small := no_large_orbit point fixed
      change Nat.card (MulAction.orbit normalizer point) < 3 at small
      omega
    have orbit_two : ∀ point ∈ MulAction.fixedPoints subgroup (Component group),
        Nat.card (MulAction.orbit normalizer point) = 2 := by
      intro point fixed
      have : Nonempty (MulAction.orbit normalizer point) :=
        ⟨⟨point, MulAction.mem_orbit_self point⟩⟩
      have positive : 0 < Nat.card (MulAction.orbit normalizer point) := Nat.card_pos
      have small := orbit_small point fixed
      by_contra not_two
      have singleton : Nat.card (MulAction.orbit normalizer point) = 1 := by omega
      exact even_point ⟨point, fixed,
        even_point_normalizer_of_singleton_orbit subgroup normalizer_even point singleton⟩
    have fixed_nonempty : Nonempty (MulAction.fixedPoints subgroup (Component group)) :=
      (Nat.card_pos_iff.mp (lt_of_lt_of_le (by decide : 0 < 3) maximal.prop.2)).1
    obtain ⟨⟨first, first_fixed⟩⟩ := fixed_nonempty
    have first_orbit_two := orbit_two first first_fixed
    have fixed_large : (MulAction.orbit normalizer first).ncard <
        (MulAction.fixedPoints subgroup (Component group)).ncard := by
      rw [← Nat.card_coe_set_eq, first_orbit_two, ← Nat.card_coe_set_eq]
      exact lt_of_lt_of_le (by decide : 2 < 3) maximal.prop.2
    obtain ⟨second, second_fixed, second_not_orbit⟩ :=
      Set.exists_mem_notMem_of_ncard_lt_ncard fixed_large
    have distinct : first ≠ second := by
      intro equal_points
      exact second_not_orbit (equal_points ▸ MulAction.mem_orbit_self first)
    have subgroup_le_pair : subgroup ≤ pairSubgroup first second := by
      intro acting mem_subgroup
      exact ⟨MulAction.mem_fixedPoints.mp first_fixed ⟨acting, mem_subgroup⟩,
        MulAction.mem_fixedPoints.mp second_fixed ⟨acting, mem_subgroup⟩⟩
    by_cases is_sylow : ∃ sylow : Sylow prime (pairSubgroup first second),
        (sylow : Subgroup (pairSubgroup first second)).map (pairSubgroup first second).subtype = subgroup
    · obtain ⟨sylow, equal_image⟩ := is_sylow
      obtain ⟨flip, normalizes, moves, _⟩ := CFSG.OrderReductions.TwoPointSylow.exists_sylow_normalizing_flip
        prime first second distinct sylow
      rw [equal_image] at normalizes
      exact second_not_orbit (MulAction.mem_orbit_iff.mpr ⟨⟨flip.val, normalizes⟩, moves⟩)
    · obtain ⟨larger, larger_prime, strictly_larger, larger_le⟩ :=
        CFSG.OrderReductions.FixedPairSylow.exists_larger_prime_subgroup_in_normalizer_within prime subgroup
          (pairSubgroup first second) subgroup_le_pair maximal.prop.1 is_sylow
      have larger_normalizes : larger ≤ normalizer := larger_le.trans inf_le_left
      have all_fixed : MulAction.fixedPoints subgroup (Component group) ⊆
          MulAction.fixedPoints larger (Component group) := by
        intro point fixed
        apply odd_prime_small_orbit_fixed prime prime_odd larger_prime point
        have orbit_subset := subgroup_orbit_subset_of_le larger normalizer larger_normalizes point
        have card_le := Nat.card_le_card_of_injective (Set.inclusion orbit_subset)
          (Set.inclusion_injective orbit_subset)
        exact card_le.trans (orbit_small point fixed)
      have card_le := Nat.card_le_card_of_injective (Set.inclusion all_fixed)
        (Set.inclusion_injective all_fixed)
      have larger_three : CFSG.OrderReductions.MaximalThreePoint.ThreePointPrime
          (points := Component group) prime larger := ⟨larger_prime, maximal.prop.2.trans card_le⟩
      exact strictly_larger.ne (maximal.eq_of_le larger_three strictly_larger.le)

theorem even_point_normalizer_of_large_orbit_and_common_image {group quotient : Type*}
    [Group group] [Finite group] [Group quotient] (prime : ℕ) [Fact (Nat.Prime prime)]
    (subgroup : Subgroup group)
    (maximal : Maximal
      (CFSG.OrderReductions.MaximalThreePoint.ThreePointPrime (points := Component group) prime) subgroup)
    (point : Component group) (point_fixed : point ∈ MulAction.fixedPoints subgroup (Component group))
    (large_orbit : 3 ≤ Nat.card (MulAction.orbit (Subgroup.normalizer (subgroup : Set group)) point))
    (homomorphism : Subgroup.normalizer (subgroup : Set group) →* quotient)
    (common : quotient) (common_order : orderOf common = 2)
    (common_image : ∀ involution : Involution (Subgroup.normalizer (subgroup : Set group)),
      homomorphism involution.val = common) :
    ∃ base ∈ MulAction.fixedPoints subgroup (Component group),
      Even (Nat.card ↥(Subgroup.normalizer (subgroup : Set group) ⊓ componentStabilizer base)) := by
  classical
  let normalizer := Subgroup.normalizer (subgroup : Set group)
  have orbit_large : 2 < (MulAction.orbit normalizer point).ncard := by
    rw [← Nat.card_coe_set_eq]
    change 3 ≤ Nat.card (MulAction.orbit normalizer point) at large_orbit
    omega
  obtain ⟨first, first_orbit, second, second_orbit, third, third_orbit,
    first_second, first_third, second_third⟩ := (Set.two_lt_ncard (Set.toFinite _)).mp orbit_large
  have orbit_fixed := normalizer_orbit_subset_fixed subgroup point point_fixed
  have first_fixed := orbit_fixed first_orbit
  have second_fixed := orbit_fixed second_orbit
  have third_fixed := orbit_fixed third_orbit
  have same_orbit (initial final : Component group)
      (initial_mem : initial ∈ MulAction.orbit normalizer point)
      (final_mem : final ∈ MulAction.orbit normalizer point) :
      ∃ element : normalizer, element.val • initial = final := by
    obtain ⟨initial_element, initial_eq⟩ := MulAction.mem_orbit_iff.mp initial_mem
    obtain ⟨final_element, final_eq⟩ := MulAction.mem_orbit_iff.mp final_mem
    refine ⟨final_element * initial_element⁻¹, ?_⟩
    change (final_element * initial_element⁻¹) • initial = final
    rw [mul_smul, ← initial_eq, inv_smul_smul, final_eq]
  obtain ⟨first_flip, first_normalizes, first_moves, _⟩ :=
    CFSG.OrderReductions.MaximalThreePoint.maximal_pair_normalizer_flip prime subgroup maximal
      first second first_second first_fixed second_fixed
      (same_orbit first second first_orbit second_orbit)
  obtain ⟨second_flip, second_normalizes, second_moves, _⟩ :=
    CFSG.OrderReductions.MaximalThreePoint.maximal_pair_normalizer_flip prime subgroup maximal
      second third second_third second_fixed third_fixed
      (same_orbit second third second_orbit third_orbit)
  obtain ⟨third_flip, third_normalizes, third_moves, _⟩ :=
    CFSG.OrderReductions.MaximalThreePoint.maximal_pair_normalizer_flip prime subgroup maximal
      third first first_third.symm third_fixed first_fixed
      (same_orbit third first third_orbit first_orbit)
  let first_internal : Involution normalizer :=
    ⟨⟨first_flip.val, first_normalizes⟩, by rw [← Subgroup.orderOf_coe]; exact first_flip.property⟩
  let second_internal : Involution normalizer :=
    ⟨⟨second_flip.val, second_normalizes⟩, by rw [← Subgroup.orderOf_coe]; exact second_flip.property⟩
  let third_internal : Involution normalizer :=
    ⟨⟨third_flip.val, third_normalizes⟩, by rw [← Subgroup.orderOf_coe]; exact third_flip.property⟩
  let product := third_internal.val * second_internal.val * first_internal.val
  have fixes_first : product.val • first = first := by
    change (third_flip.val * second_flip.val * first_flip.val) • first = first
    rw [mul_smul, mul_smul, first_moves, second_moves, third_moves]
  have common_square : common * common = 1 := by
    simpa only [common_order, pow_two] using pow_orderOf_eq_one common
  have product_image : homomorphism product = common := by
    change homomorphism (third_internal.val * second_internal.val * first_internal.val) = common
    rw [map_mul, map_mul, common_image, common_image, common_image, common_square, one_mul]
  have even_order : 2 ∣ orderOf product := by
    have divides := orderOf_map_dvd homomorphism product
    rwa [product_image, common_order] at divides
  have divides := Subgroup.orderOf_dvd_natCard (normalizer ⊓ componentStabilizer first)
    (show product.val ∈ normalizer ⊓ componentStabilizer first from ⟨product.property, fixes_first⟩)
  change 2 ∣ orderOf (product : normalizer) at even_order
  rw [← Subgroup.orderOf_coe] at even_order
  exact ⟨first, first_fixed, even_iff_two_dvd.mpr (even_order.trans divides)⟩

theorem maximal_even_point_normalizer_of_common_image {group quotient : Type*}
    [Group group] [Finite group] [Group quotient] (prime : ℕ) [Fact (Nat.Prime prime)]
    (prime_odd : Odd prime) (subgroup : Subgroup group)
    (maximal : Maximal
      (CFSG.OrderReductions.MaximalThreePoint.ThreePointPrime (points := Component group) prime) subgroup)
    (homomorphism : Subgroup.normalizer (subgroup : Set group) →* quotient)
    (common : quotient) (common_order : orderOf common = 2)
    (common_image : ∀ involution : Involution (Subgroup.normalizer (subgroup : Set group)),
      homomorphism involution.val = common) :
    ∃ point ∈ MulAction.fixedPoints subgroup (Component group),
      Even (Nat.card ↥(Subgroup.normalizer (subgroup : Set group) ⊓ componentStabilizer point)) := by
  rcases maximal_large_orbit_or_even_point_normalizer prime prime_odd subgroup maximal with
    even_point | ⟨point, fixed, large⟩
  · exact even_point
  · exact even_point_normalizer_of_large_orbit_and_common_image prime subgroup maximal
      point fixed large homomorphism common common_order common_image

theorem maximal_even_point_normalizer_of_central_images {group quotient : Type*}
    [Group group] [Finite group] [Group quotient] (prime : ℕ) [Fact (Nat.Prime prime)]
    (prime_odd : Odd prime) (subgroup : Subgroup group)
    (maximal : Maximal
      (CFSG.OrderReductions.MaximalThreePoint.ThreePointPrime (points := Component group) prime) subgroup)
    (homomorphism : Subgroup.normalizer (subgroup : Set group) →* quotient)
    (surjective : Function.Surjective homomorphism)
    (odd_kernel : Odd (Nat.card homomorphism.ker))
    (no_four : ∀ first second : Involution (Subgroup.normalizer (subgroup : Set group)),
      Commute first.val second.val → first = second)
    (central_images : ∀ involution : Involution (Subgroup.normalizer (subgroup : Set group)),
      homomorphism involution.val ∈ Subgroup.center quotient) :
    ∃ point ∈ MulAction.fixedPoints subgroup (Component group),
      Even (Nat.card ↥(Subgroup.normalizer (subgroup : Set group) ⊓ componentStabilizer point)) := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  have normalizer_even := CFSG.OrderReductions.MaximalThreePoint.maximal_normalizer_even prime subgroup maximal
  obtain ⟨element, element_order⟩ := exists_prime_orderOf_dvd_card' 2 normalizer_even.two_dvd
  let involution : Involution (Subgroup.normalizer (subgroup : Set group)) := ⟨element, element_order⟩
  apply maximal_even_point_normalizer_of_common_image prime prime_odd subgroup maximal homomorphism
    (homomorphism involution.val)
    (CFSG.OrderReductions.OddKernelInvolutions.involution_image_order homomorphism odd_kernel involution)
  intro other
  exact CFSG.OrderReductions.OddKernelInvolutions.common_involution_image_of_central_and_no_four
    homomorphism surjective odd_kernel no_four central_images other involution

end CFSG.OrderReductions.EvenPointNormalizer
