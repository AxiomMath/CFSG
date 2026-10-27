module

public import CFSG.Assembly.OrderReductions.InvolutiveIntersection

public section

namespace CFSG.OrderReductions.InvariantOrbitBound

open CFSG.OrderReductions.PrimePart
open CFSG.OrderReductions.InvolutiveIntersection

@[expose] noncomputable def fixedIndex {group : Type*} [Group group]
    (automorphism : MulAut group) (subgroup : Subgroup group) : ℕ :=
  (CFSG.OrderReductions.OddInversion.fixedSubgroup automorphism).relIndex subgroup

theorem fixedIndex_mul_fixed_card {group : Type*} [Group group] [Finite group]
    (automorphism : MulAut group) (subgroup : Subgroup group) :
    fixedIndex automorphism subgroup *
      Nat.card ↥(subgroup ⊓ CFSG.OrderReductions.OddInversion.fixedSubgroup automorphism) =
        Nat.card subgroup := by
  have card_eq := ((CFSG.OrderReductions.OddInversion.fixedSubgroup automorphism).subgroupOf subgroup).card_mul_index
  have fixed_card : Nat.card ((CFSG.OrderReductions.OddInversion.fixedSubgroup automorphism).subgroupOf subgroup) =
      Nat.card ↥(subgroup ⊓ CFSG.OrderReductions.OddInversion.fixedSubgroup automorphism) := by
    rw [← Subgroup.card_map_of_injective
      (K := (CFSG.OrderReductions.OddInversion.fixedSubgroup automorphism).subgroupOf subgroup)
      (f := subgroup.subtype) Subtype.val_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [fixed_card, mul_comm] at card_eq
  exact card_eq

theorem primePart_fixedIndex_mul_fixed_part {group : Type*} [Group group] [Finite group]
    (prime : ℕ) (automorphism : MulAut group) (subgroup : Subgroup group) :
    primePart prime (fixedIndex automorphism subgroup) *
      primePart prime (Nat.card ↥(subgroup ⊓ CFSG.OrderReductions.OddInversion.fixedSubgroup automorphism)) =
        primePart prime (Nat.card subgroup) := by
  have index_ne : fixedIndex automorphism subgroup ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
      (H := (CFSG.OrderReductions.OddInversion.fixedSubgroup automorphism).subgroupOf subgroup)
  rw [← primePart_mul prime _ _ index_ne (ne_of_gt (Nat.card_pos (α :=
      ↥(subgroup ⊓ CFSG.OrderReductions.OddInversion.fixedSubgroup automorphism)))),
    fixedIndex_mul_fixed_card]

theorem fixedIndex_mono {group : Type*} [Group group] [Finite group]
    (automorphism : MulAut group) (smaller larger : Subgroup group) (contains : smaller ≤ larger) :
    fixedIndex automorphism smaller ≤ fixedIndex automorphism larger :=
  Subgroup.relIndex_le_of_le_right contains
    (Subgroup.index_ne_zero_of_finite
      (H := (CFSG.OrderReductions.OddInversion.fixedSubgroup automorphism).subgroupOf larger))

theorem exists_invariant_intersection_sylow_containing {group : Type*}
    [Group group] [Finite group] (prime : ℕ) [Fact (Nat.Prime prime)]
    (automorphism : MulAut group) (involutive : Function.Involutive automorphism)
    (subgroup : Subgroup group) (odd_subgroup : Odd (Nat.card subgroup))
    (prime_subgroup : Subgroup group) (prime_group : IsPGroup prime prime_subgroup)
    (contains : prime_subgroup ≤ subgroup)
    (invariant : prime_subgroup.map automorphism.toMonoidHom = prime_subgroup) :
    ∃ sylow : Sylow prime (intersection automorphism subgroup),
      prime_subgroup ≤ (sylow : Subgroup (intersection automorphism subgroup)).map
        (intersection automorphism subgroup).subtype ∧
      ((sylow : Subgroup (intersection automorphism subgroup)).map
        (intersection automorphism subgroup).subtype).map automorphism.toMonoidHom =
        (sylow : Subgroup (intersection automorphism subgroup)).map
          (intersection automorphism subgroup).subtype := by
  let common := intersection automorphism subgroup
  have common_invariant := intersection_invariant automorphism involutive subgroup
  have common_contains := invariant_le_intersection automorphism subgroup prime_subgroup
    contains invariant
  have common_odd : Odd (Nat.card common) := odd_subgroup.of_dvd_nat
    (Subgroup.card_dvd_of_le (show common ≤ subgroup from inf_le_left))
  let restricted := CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism automorphism common
    common_invariant
  have restricted_prime : IsPGroup prime (prime_subgroup.subgroupOf common) :=
    prime_group.of_equiv (Subgroup.subgroupOfEquivOfLe common_contains).symm
  obtain ⟨sylow, internal_contains, internal_invariant⟩ :=
    CFSG.OrderReductions.InvariantSylow.exists_invariant_sylow_containing_of_odd prime common_odd restricted
      (CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism_involutive automorphism involutive
        common common_invariant) (prime_subgroup.subgroupOf common) restricted_prime
      (CFSG.OrderReductions.InvariantSylow.subgroupOf_invariant automorphism prime_subgroup common
        common_contains common_invariant invariant)
  refine ⟨sylow, ?_, ?_⟩
  · rw [← Subgroup.map_subgroupOf_eq_of_le common_contains]
    exact Subgroup.map_mono internal_contains
  · exact CFSG.OrderReductions.InvariantSylow.map_subtype_invariant automorphism common common_invariant
      sylow internal_invariant

theorem invariant_sylow_index_mul_fixed_part {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (automorphism : MulAut group)
    (involutive : Function.Involutive automorphism) (subgroup : Subgroup group)
    (odd_subgroup : Odd (Nat.card subgroup))
    (sylow : Sylow prime (intersection automorphism subgroup))
    (invariant :
      ((sylow : Subgroup (intersection automorphism subgroup)).map
        (intersection automorphism subgroup).subtype).map automorphism.toMonoidHom =
        (sylow : Subgroup (intersection automorphism subgroup)).map
          (intersection automorphism subgroup).subtype) :
    fixedIndex automorphism ((sylow : Subgroup (intersection automorphism subgroup)).map
      (intersection automorphism subgroup).subtype) *
        primePart prime (Nat.card ↥(subgroup ⊓ CFSG.OrderReductions.OddInversion.fixedSubgroup automorphism)) =
          primePart prime (Nat.card (intersection automorphism subgroup)) := by
  have card_eq := fixedIndex_mul_fixed_card automorphism
    ((sylow : Subgroup (intersection automorphism subgroup)).map
      (intersection automorphism subgroup).subtype)
  rw [invariant_intersection_fixed_card prime automorphism involutive subgroup odd_subgroup
    sylow invariant, sylow_map_card_eq_primePart] at card_eq
  exact card_eq

theorem invariant_prime_index_le {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (automorphism : MulAut group)
    (involutive : Function.Involutive automorphism) (subgroup : Subgroup group)
    (odd_subgroup : Odd (Nat.card subgroup))
    (prime_subgroup : Subgroup group) (prime_group : IsPGroup prime prime_subgroup)
    (contains : prime_subgroup ≤ subgroup)
    (invariant : prime_subgroup.map automorphism.toMonoidHom = prime_subgroup) :
    fixedIndex automorphism prime_subgroup ≤ primePart prime (fixedIndex automorphism subgroup) := by
  obtain ⟨sylow, image_contains, image_invariant⟩ := exists_invariant_intersection_sylow_containing
    prime automorphism involutive subgroup odd_subgroup prime_subgroup prime_group contains invariant
  apply (fixedIndex_mono automorphism _ _ image_contains).trans
  have image_product := invariant_sylow_index_mul_fixed_part prime automorphism involutive subgroup
    odd_subgroup sylow image_invariant
  have full_product := primePart_fixedIndex_mul_fixed_part prime automorphism subgroup
  have parts_le := primePart_subgroup_le prime (intersection automorphism subgroup) subgroup inf_le_left
  apply Nat.le_of_mul_le_mul_right (c := primePart prime
    (Nat.card ↥(subgroup ⊓ CFSG.OrderReductions.OddInversion.fixedSubgroup automorphism)))
  · rw [image_product, full_product]
    exact parts_le
  · exact pow_pos (Fact.out : Nat.Prime prime).pos _

theorem invariant_prime_index_ge_extends_sylow {group : Type*}
    [Group group] [Finite group] (prime : ℕ) [Fact (Nat.Prime prime)]
    (automorphism : MulAut group) (involutive : Function.Involutive automorphism)
    (subgroup : Subgroup group) (odd_subgroup : Odd (Nat.card subgroup))
    (prime_subgroup : Subgroup group) (prime_group : IsPGroup prime prime_subgroup)
    (contains : prime_subgroup ≤ subgroup)
    (invariant : prime_subgroup.map automorphism.toMonoidHom = prime_subgroup)
    (large_index : primePart prime (fixedIndex automorphism subgroup) ≤
      fixedIndex automorphism prime_subgroup) :
    ∃ sylow : Sylow prime subgroup,
      let image := (sylow : Subgroup subgroup).map subgroup.subtype
      prime_subgroup ≤ image ∧ image.map automorphism.toMonoidHom = image ∧
        fixedIndex automorphism prime_subgroup = primePart prime (fixedIndex automorphism subgroup) ∧
          fixedIndex automorphism image = primePart prime (fixedIndex automorphism subgroup) := by
  obtain ⟨internal, image_contains, image_invariant⟩ := exists_invariant_intersection_sylow_containing
    prime automorphism involutive subgroup odd_subgroup prime_subgroup prime_group contains invariant
  let image := (internal : Subgroup (intersection automorphism subgroup)).map
    (intersection automorphism subgroup).subtype
  have image_product := invariant_sylow_index_mul_fixed_part prime automorphism involutive subgroup
    odd_subgroup internal image_invariant
  have full_product := primePart_fixedIndex_mul_fixed_part prime automorphism subgroup
  have parts_le := primePart_subgroup_le prime (intersection automorphism subgroup) subgroup inf_le_left
  have image_index_le : fixedIndex automorphism image ≤
      primePart prime (fixedIndex automorphism subgroup) := by
    apply Nat.le_of_mul_le_mul_right (c := primePart prime
      (Nat.card ↥(subgroup ⊓ CFSG.OrderReductions.OddInversion.fixedSubgroup automorphism)))
    · rw [image_product, full_product]
      exact parts_le
    · exact pow_pos (Fact.out : Nat.Prime prime).pos _
  have prime_index_le := fixedIndex_mono automorphism prime_subgroup image image_contains
  have image_index_equal : fixedIndex automorphism image =
      primePart prime (fixedIndex automorphism subgroup) :=
    le_antisymm image_index_le (large_index.trans prime_index_le)
  have equal_parts : primePart prime (Nat.card (intersection automorphism subgroup)) =
      primePart prime (Nat.card subgroup) := by
    rw [← image_product, image_index_equal, full_product]
  have image_le : image ≤ subgroup := by
    intro element mem_image
    obtain ⟨original, _, equal_image⟩ := Subgroup.mem_map.mp mem_image
    exact equal_image ▸ original.property.1
  have image_card : Nat.card image = primePart prime (Nat.card subgroup) :=
    (sylow_map_card_eq_primePart prime (intersection automorphism subgroup) internal).trans equal_parts
  obtain ⟨sylow, sylow_image⟩ := exists_sylow_image_of_card prime image subgroup image_le image_card
  refine ⟨sylow, ?_⟩
  dsimp only
  rw [sylow_image]
  exact ⟨image_contains, image_invariant,
    le_antisymm (prime_index_le.trans image_index_le) large_index, image_index_equal⟩

theorem invariant_sylow_index_eq {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (automorphism : MulAut group)
    (involutive : Function.Involutive automorphism) (subgroup : Subgroup group)
    (odd_subgroup : Odd (Nat.card subgroup)) (sylow : Sylow prime subgroup)
    (invariant : ((sylow : Subgroup subgroup).map subgroup.subtype).map
      automorphism.toMonoidHom = (sylow : Subgroup subgroup).map subgroup.subtype) :
    fixedIndex automorphism ((sylow : Subgroup subgroup).map subgroup.subtype) =
      primePart prime (fixedIndex automorphism subgroup) := by
  have equal_parts := (invariant_sylow_intersection_iff prime automorphism involutive subgroup
    odd_subgroup).mpr ⟨sylow, invariant⟩
  let image := (sylow : Subgroup subgroup).map subgroup.subtype
  have image_le : image ≤ intersection automorphism subgroup := by
    apply invariant_le_intersection automorphism subgroup image ?_ invariant
    intro element mem_image
    obtain ⟨original, _, equal_image⟩ := Subgroup.mem_map.mp mem_image
    exact equal_image ▸ original.property
  have image_card : Nat.card image = primePart prime (Nat.card (intersection automorphism subgroup)) :=
    (sylow_map_card_eq_primePart prime subgroup sylow).trans equal_parts.symm
  obtain ⟨internal, internal_image⟩ := exists_sylow_image_of_card prime image
    (intersection automorphism subgroup) image_le image_card
  have internal_invariant :
      ((internal : Subgroup (intersection automorphism subgroup)).map
        (intersection automorphism subgroup).subtype).map automorphism.toMonoidHom =
        (internal : Subgroup (intersection automorphism subgroup)).map
          (intersection automorphism subgroup).subtype := by
    rw [internal_image]
    exact invariant
  have image_product := invariant_sylow_index_mul_fixed_part prime automorphism involutive subgroup
    odd_subgroup internal internal_invariant
  rw [internal_image, equal_parts] at image_product
  have full_product := primePart_fixedIndex_mul_fixed_part prime automorphism subgroup
  exact Nat.eq_of_mul_eq_mul_right (pow_pos (Fact.out : Nat.Prime prime).pos _)
    (image_product.trans full_product.symm)

theorem invariant_prime_index_criterion {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (automorphism : MulAut group)
    (involutive : Function.Involutive automorphism) (subgroup : Subgroup group)
    (odd_subgroup : Odd (Nat.card subgroup)) :
    (∃ sylow : Sylow prime subgroup,
      ((sylow : Subgroup subgroup).map subgroup.subtype).map automorphism.toMonoidHom =
        (sylow : Subgroup subgroup).map subgroup.subtype) ↔
    ∃ prime_subgroup : Subgroup group, IsPGroup prime prime_subgroup ∧ prime_subgroup ≤ subgroup ∧
      prime_subgroup.map automorphism.toMonoidHom = prime_subgroup ∧
      primePart prime (fixedIndex automorphism subgroup) ≤ fixedIndex automorphism prime_subgroup := by
  constructor
  · rintro ⟨sylow, invariant⟩
    let image := (sylow : Subgroup subgroup).map subgroup.subtype
    refine ⟨image, sylow.isPGroup'.map subgroup.subtype, ?_, invariant, ?_⟩
    · intro element mem_image
      obtain ⟨original, _, equal_image⟩ := Subgroup.mem_map.mp mem_image
      exact equal_image ▸ original.property
    · exact (invariant_sylow_index_eq prime automorphism involutive subgroup odd_subgroup
        sylow invariant).ge
  · rintro ⟨prime_subgroup, prime_group, contains, invariant, large_index⟩
    obtain ⟨sylow, _, sylow_invariant, _, _⟩ := invariant_prime_index_ge_extends_sylow
      prime automorphism involutive subgroup odd_subgroup prime_subgroup prime_group contains
      invariant large_index
    exact ⟨sylow, sylow_invariant⟩

end CFSG.OrderReductions.InvariantOrbitBound
