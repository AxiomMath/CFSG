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
public import CFSG.Assembly.OrderReductions.InvariantSylow
public import CFSG.Assembly.OrderReductions.FixedPointLifting
public import CFSG.Assembly.OrderReductions.InvariantQuotient
public import CFSG.Assembly.OrderReductions.PrimePart

public section

namespace CFSG.OrderReductions.FourGroupGeneration

@[expose] def FixedGeneration {group : Type*} [Group group] (first second : MulAut group) : Prop :=
  ∀ subgroup : Subgroup group,
    (∀ element : group, first element = element → element ∈ subgroup) →
    (∀ element : group, second element = element → element ∈ subgroup) →
    (∀ element : group, first (second element) = element → element ∈ subgroup) →
    subgroup = ⊤

theorem odd_abelian_involution_decomposition {group : Type*} [CommGroup group] [Finite group]
    (odd_group : Odd (Nat.card group)) (automorphism : MulAut group)
    (involutive : Function.Involutive automorphism) (element : group) :
    ∃ fixed inverted : group, automorphism fixed = fixed ∧
      automorphism inverted = inverted⁻¹ ∧ element = fixed * inverted := by
  obtain ⟨root, root_square⟩ := odd_group.coprime_two_right.pow_left_bijective.surjective element
  change root ^ 2 = element at root_square
  refine ⟨root * automorphism root, root * (automorphism root)⁻¹, ?_, ?_, ?_⟩
  · rw [map_mul, involutive, mul_comm]
  · rw [map_mul, map_inv, involutive, mul_inv_rev, inv_inv]
  · rw [mul_mul_mul_comm, mul_inv_cancel, mul_one, ← pow_two, root_square]

theorem odd_abelian_four_involution_generation {group : Type*}
    [CommGroup group] [Finite group] (odd_group : Odd (Nat.card group))
    (first second : MulAut group) (first_involutive : Function.Involutive first)
    (second_involutive : Function.Involutive second)
    (commutes : ∀ element : group, first (second element) = second (first element))
    (subgroup : Subgroup group)
    (first_fixed : ∀ element : group, first element = element → element ∈ subgroup)
    (second_fixed : ∀ element : group, second element = element → element ∈ subgroup)
    (product_fixed : ∀ element : group, first (second element) = element → element ∈ subgroup) :
    subgroup = ⊤ := by
  apply top_unique
  intro element _
  obtain ⟨fixed, inverted, fixed_first, inverted_first, product_eq⟩ :=
    odd_abelian_involution_decomposition odd_group first first_involutive element
  obtain ⟨root, root_square⟩ := odd_group.coprime_two_right.pow_left_bijective.surjective inverted
  change root ^ 2 = inverted at root_square
  have root_inverted : first root = root⁻¹ := by
    apply odd_group.coprime_two_right.pow_left_bijective.injective
    change (first root) ^ 2 = (root⁻¹) ^ 2
    rw [← map_pow, root_square, inverted_first, inv_pow, root_square]
  let fixed_second := root * second root
  let inverted_second := root * (second root)⁻¹
  have fixed_second_fixed : second fixed_second = fixed_second := by
    change second (root * second root) = root * second root
    rw [map_mul, second_involutive, mul_comm]
  have inverted_second_inverted : second inverted_second = inverted_second⁻¹ := by
    change second (root * (second root)⁻¹) = (root * (second root)⁻¹)⁻¹
    rw [map_mul, map_inv, second_involutive, mul_inv_rev, inv_inv]
  have inverted_first_fixed : first inverted_second = inverted_second⁻¹ := by
    change first (root * (second root)⁻¹) = (root * (second root)⁻¹)⁻¹
    rw [map_mul, map_inv, commutes, root_inverted, map_inv, inv_inv, mul_inv_rev, inv_inv, mul_comm]
  have product_involution_fixed : first (second inverted_second) = inverted_second := by
    rw [inverted_second_inverted, map_inv, inverted_first_fixed, inv_inv]
  have inverted_product : inverted = fixed_second * inverted_second := by
    change inverted = (root * second root) * (root * (second root)⁻¹)
    rw [mul_mul_mul_comm, mul_inv_cancel, mul_one, ← pow_two, root_square]
  rw [product_eq, inverted_product]
  exact subgroup.mul_mem (first_fixed fixed fixed_first)
    (subgroup.mul_mem (second_fixed fixed_second fixed_second_fixed)
      (product_fixed inverted_second product_involution_fixed))

theorem odd_abelian_fixedGeneration {group : Type*} [CommGroup group] [Finite group]
    (odd_group : Odd (Nat.card group)) (first second : MulAut group)
    (first_involutive : Function.Involutive first)
    (second_involutive : Function.Involutive second)
    (commutes : ∀ element : group, first (second element) = second (first element)) :
    FixedGeneration first second :=
  odd_abelian_four_involution_generation odd_group first second first_involutive
    second_involutive commutes

theorem product_involutive {group : Type*} [Group group] (first second : MulAut group)
    (first_involutive : Function.Involutive first)
    (second_involutive : Function.Involutive second)
    (commutes : ∀ element : group, first (second element) = second (first element)) :
    Function.Involutive (first * second : MulAut group) := by
  intro element
  change first (second (first (second element))) = element
  rw [← commutes, first_involutive, second_involutive]

theorem fixedGeneration_normal_extension {group : Type*} [Group group] [Finite group]
    (first second : MulAut group) (first_involutive : Function.Involutive first)
    (second_involutive : Function.Involutive second)
    (commutes : ∀ element : group, first (second element) = second (first element))
    (normal : Subgroup group) [normal.Normal] (odd_normal : Odd (Nat.card normal))
    (first_invariant : normal.map first.toMonoidHom = normal)
    (second_invariant : normal.map second.toMonoidHom = normal)
    (normal_generation : FixedGeneration
      (CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism first normal first_invariant)
      (CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism second normal second_invariant))
    (quotient_generation : FixedGeneration
      (CFSG.OrderReductions.InvariantQuotient.quotientAutomorphism first normal first_invariant)
      (CFSG.OrderReductions.InvariantQuotient.quotientAutomorphism second normal second_invariant)) :
    FixedGeneration first second := by
  intro subgroup first_fixed second_fixed product_fixed
  have normal_le : normal ≤ subgroup := by
    apply Subgroup.subgroupOf_eq_top.mp
    apply normal_generation
    · intro element fixed
      exact first_fixed element.val (congrArg Subtype.val fixed)
    · intro element fixed
      exact second_fixed element.val (congrArg Subtype.val fixed)
    · intro element fixed
      exact product_fixed element.val (congrArg Subtype.val fixed)
  let projection := QuotientGroup.mk' normal
  let quotient_first :=
    CFSG.OrderReductions.InvariantQuotient.quotientAutomorphism first normal first_invariant
  let quotient_second :=
    CFSG.OrderReductions.InvariantQuotient.quotientAutomorphism second normal second_invariant
  have odd_kernel : Odd (Nat.card projection.ker) := by
    change Odd (Nat.card (QuotientGroup.mk' normal).ker)
    rwa [QuotientGroup.ker_mk']
  have first_equivariant : ∀ element : group,
      projection (first element) = quotient_first (projection element) := by
    intro element
    exact (CFSG.OrderReductions.InvariantQuotient.quotientAutomorphism_apply
      first normal first_invariant element).symm
  have second_equivariant : ∀ element : group,
      projection (second element) = quotient_second (projection element) := by
    intro element
    exact (CFSG.OrderReductions.InvariantQuotient.quotientAutomorphism_apply
      second normal second_invariant element).symm
  have product_equivariant : ∀ element : group,
      projection ((first * second : MulAut group) element) =
        (quotient_first * quotient_second : MulAut (group ⧸ normal)) (projection element) := by
    intro element
    change projection (first (second element)) = quotient_first (quotient_second (projection element))
    rw [first_equivariant, second_equivariant]
  have image_top : subgroup.map projection = ⊤ := by
    apply quotient_generation
    · intro point fixed
      obtain ⟨element, image_eq, element_fixed⟩ :=
        CFSG.OrderReductions.FixedPointLifting.exists_fixed_lift_of_odd_kernel first quotient_first
          first_involutive projection (QuotientGroup.mk'_surjective normal) odd_kernel
          first_equivariant point fixed
      exact Subgroup.mem_map.mpr ⟨element, first_fixed element element_fixed, image_eq⟩
    · intro point fixed
      obtain ⟨element, image_eq, element_fixed⟩ :=
        CFSG.OrderReductions.FixedPointLifting.exists_fixed_lift_of_odd_kernel second quotient_second
          second_involutive projection (QuotientGroup.mk'_surjective normal) odd_kernel
          second_equivariant point fixed
      exact Subgroup.mem_map.mpr ⟨element, second_fixed element element_fixed, image_eq⟩
    · intro point fixed
      obtain ⟨element, image_eq, element_fixed⟩ :=
        CFSG.OrderReductions.FixedPointLifting.exists_fixed_lift_of_odd_kernel
          (first * second) (quotient_first * quotient_second)
          (product_involutive first second first_involutive second_involutive commutes)
          projection (QuotientGroup.mk'_surjective normal) odd_kernel
          product_equivariant point fixed
      exact Subgroup.mem_map.mpr ⟨element, product_fixed element element_fixed, image_eq⟩
  have kernel_le : projection.ker ≤ subgroup := by
    change (QuotientGroup.mk' normal).ker ≤ subgroup
    rwa [QuotientGroup.ker_mk']
  have comap_top := congrArg (Subgroup.comap projection) image_top
  rwa [Subgroup.comap_map_eq_self kernel_le, Subgroup.comap_top] at comap_top

theorem odd_pGroup_fixedGeneration {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (prime_group : IsPGroup prime group)
    (odd_group : Odd (Nat.card group)) (first second : MulAut group)
    (first_involutive : Function.Involutive first)
    (second_involutive : Function.Involutive second)
    (commutes : ∀ element : group, first (second element) = second (first element)) :
    FixedGeneration first second := by
  classical
  generalize order_eq : Nat.card group = order
  induction order using Nat.strong_induction_on generalizing group with
  | h order induction_hypothesis =>
      by_cases trivial : Subsingleton group
      · let := trivial
        intro subgroup _ _ _
        apply top_unique
        intro element _
        simpa only [Subsingleton.elim element 1] using subgroup.one_mem
      · have : Nontrivial group := not_subsingleton_iff_nontrivial.mp trivial
        let center := Subgroup.center group
        have center_nontrivial : Nontrivial center := prime_group.center_nontrivial
        let : CommGroup center :=
          { toGroup := inferInstance
            mul_comm := fun first_element second_element =>
              Subtype.ext ((Subgroup.mem_center_iff.mp second_element.property) first_element.val) }
        have center_odd : Odd (Nat.card center) :=
          odd_group.of_dvd_nat center.card_subgroup_dvd_card
        have first_invariant : center.map first.toMonoidHom = center :=
          Subgroup.characteristic_iff_map_eq.mp (inferInstance : center.Characteristic) first
        have second_invariant : center.map second.toMonoidHom = center :=
          Subgroup.characteristic_iff_map_eq.mp (inferInstance : center.Characteristic) second
        have center_generation : FixedGeneration
            (CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism first center first_invariant)
            (CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism second center second_invariant) :=
          odd_abelian_fixedGeneration center_odd _ _
            (CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism_involutive
              first first_involutive center first_invariant)
            (CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism_involutive
              second second_involutive center second_invariant)
            (CFSG.OrderReductions.InvariantQuotient.restrictedAutomorphism_commutes
              first second commutes center first_invariant second_invariant)
        have center_gt_one : 1 < Nat.card center :=
          center.one_lt_card_iff_ne_bot.mpr (center.nontrivial_iff_ne_bot.mp center_nontrivial)
        have quotient_smaller : Nat.card (group ⧸ center) < order := by
          have quotient_positive : 0 < Nat.card (group ⧸ center) := Nat.card_pos
          have product_eq := center.card_eq_card_quotient_mul_card_subgroup
          rw [order_eq] at product_eq
          nlinarith
        have quotient_prime := prime_group.of_surjective (QuotientGroup.mk' center)
          (QuotientGroup.mk'_surjective center)
        have quotient_odd : Odd (Nat.card (group ⧸ center)) :=
          odd_group.of_dvd_nat center.card_quotient_dvd_card
        have quotient_generation : FixedGeneration
            (CFSG.OrderReductions.InvariantQuotient.quotientAutomorphism first center first_invariant)
            (CFSG.OrderReductions.InvariantQuotient.quotientAutomorphism second center second_invariant) :=
          induction_hypothesis (Nat.card (group ⧸ center)) quotient_smaller quotient_prime quotient_odd
            _ _
            (CFSG.OrderReductions.InvariantQuotient.quotientAutomorphism_involutive
              first first_involutive center first_invariant)
            (CFSG.OrderReductions.InvariantQuotient.quotientAutomorphism_involutive
              second second_involutive center second_invariant)
            (CFSG.OrderReductions.InvariantQuotient.quotientAutomorphism_commutes
              first second commutes center first_invariant second_invariant) rfl
        exact fixedGeneration_normal_extension first second first_involutive second_involutive
          commutes center center_odd first_invariant second_invariant
          center_generation quotient_generation

theorem exists_common_invariant_sylow {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (odd_group : Odd (Nat.card group))
    (first second : MulAut group) (first_involutive : Function.Involutive first)
    (second_involutive : Function.Involutive second)
    (commutes : ∀ element : group, first (second element) = second (first element)) :
    ∃ sylow : Sylow prime group,
      (sylow : Subgroup group).map first.toMonoidHom = sylow ∧
      (sylow : Subgroup group).map second.toMonoidHom = sylow := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  let actor := Subgroup.zpowers first × Subgroup.zpowers second
  have first_square : first ^ 2 = 1 := by
    ext element
    exact first_involutive element
  have second_square : second ^ 2 = 1 := by
    ext element
    exact second_involutive element
  have first_card : Nat.card (Subgroup.zpowers first) ∣ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one first_square
  have second_card : Nat.card (Subgroup.zpowers second) ∣ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one second_square
  have prime_actor : IsPGroup 2 actor := by
    apply IsPGroup.of_card_dvd_pow (n := 2)
    change Nat.card (Subgroup.zpowers first × Subgroup.zpowers second) ∣ 2 ^ 2
    rw [Nat.card_prod]
    exact Nat.mul_dvd_mul first_card second_card
  have automorphisms_commute : Commute first second := by
    apply MulEquiv.ext
    exact commutes
  let action : actor →* MulAut group :=
    (Subgroup.zpowers first).subtype.noncommCoprod (Subgroup.zpowers second).subtype (by
      intro first_power second_power
      obtain ⟨first_exponent, first_eq⟩ := Subgroup.mem_zpowers_iff.mp first_power.property
      obtain ⟨second_exponent, second_eq⟩ := Subgroup.mem_zpowers_iff.mp second_power.property
      change Commute first_power.val second_power.val
      rw [← first_eq, ← second_eq]
      exact automorphisms_commute.zpow_zpow first_exponent second_exponent)
  obtain ⟨sylow, invariant⟩ := CFSG.OrderReductions.InvariantSylow.exists_invariant_sylow_of_coprime
    2 prime prime_actor odd_group.not_two_dvd_nat action
  refine ⟨sylow, ?_, ?_⟩
  · have fixes := invariant (⟨first, Subgroup.mem_zpowers first⟩, 1)
    change (sylow : Subgroup group).map
      (first * (1 : MulAut group)).toMonoidHom = sylow at fixes
    simpa only [mul_one] using fixes
  · have fixes := invariant (1, ⟨second, Subgroup.mem_zpowers second⟩)
    change (sylow : Subgroup group).map
      ((1 : MulAut group) * second).toMonoidHom = sylow at fixes
    simpa only [one_mul] using fixes

theorem odd_fixedGeneration {group : Type*} [Group group] [Finite group]
    (odd_group : Odd (Nat.card group)) (first second : MulAut group)
    (first_involutive : Function.Involutive first)
    (second_involutive : Function.Involutive second)
    (commutes : ∀ element : group, first (second element) = second (first element)) :
    FixedGeneration first second := by
  intro subgroup first_fixed second_fixed product_fixed
  apply CFSG.OrderReductions.PrimePart.eq_top_of_contains_sylow_for_every_prime
  intro prime prime_is_prime
  have : Fact (Nat.Prime prime) := ⟨prime_is_prime⟩
  obtain ⟨sylow, first_invariant, second_invariant⟩ := exists_common_invariant_sylow
    prime odd_group first second first_involutive second_involutive commutes
  refine ⟨sylow, ?_⟩
  apply Subgroup.subgroupOf_eq_top.mp
  apply odd_pGroup_fixedGeneration prime sylow.isPGroup'
    (odd_group.of_dvd_nat (sylow : Subgroup group).card_subgroup_dvd_card)
    (CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism first sylow first_invariant)
    (CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism second sylow second_invariant)
    (CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism_involutive
      first first_involutive sylow first_invariant)
    (CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism_involutive
      second second_involutive sylow second_invariant)
    (CFSG.OrderReductions.InvariantQuotient.restrictedAutomorphism_commutes
      first second commutes sylow first_invariant second_invariant)
  · intro element fixed
    exact first_fixed element.val (congrArg Subtype.val fixed)
  · intro element fixed
    exact second_fixed element.val (congrArg Subtype.val fixed)
  · intro element fixed
    exact product_fixed element.val (congrArg Subtype.val fixed)

theorem odd_four_involution_generation {group : Type*} [Group group] [Finite group]
    (odd_group : Odd (Nat.card group)) (first second : MulAut group)
    (first_involutive : Function.Involutive first)
    (second_involutive : Function.Involutive second)
    (commutes : ∀ element : group, first (second element) = second (first element))
    (subgroup : Subgroup group)
    (first_fixed : ∀ element : group, first element = element → element ∈ subgroup)
    (second_fixed : ∀ element : group, second element = element → element ∈ subgroup)
    (product_fixed : ∀ element : group, first (second element) = element → element ∈ subgroup) :
    subgroup = ⊤ :=
  odd_fixedGeneration odd_group first second first_involutive second_involutive commutes
    subgroup first_fixed second_fixed product_fixed

end CFSG.OrderReductions.FourGroupGeneration
