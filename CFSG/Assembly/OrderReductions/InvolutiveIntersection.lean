module

public import CFSG.Assembly.OrderReductions.CoprimeFixedSubgroup
public import CFSG.Assembly.OrderReductions.PrimePart
public import CFSG.Assembly.OrderReductions.OddInversion

public section

namespace CFSG.OrderReductions.InvolutiveIntersection

open CFSG.OrderReductions.PrimePart

open scoped Pointwise

@[expose] def intersection {group : Type*} [Group group]
    (automorphism : MulAut group) (subgroup : Subgroup group) : Subgroup group :=
  subgroup ⊓ subgroup.map automorphism.toMonoidHom

theorem intersection_invariant {group : Type*} [Group group]
    (automorphism : MulAut group) (involutive : Function.Involutive automorphism)
    (subgroup : Subgroup group) :
    (intersection automorphism subgroup).map automorphism.toMonoidHom =
      intersection automorphism subgroup := by
  have composite : automorphism.toMonoidHom.comp automorphism.toMonoidHom =
      MonoidHom.id group := by
    ext element
    exact involutive element
  rw [intersection, Subgroup.map_inf _ _ _ automorphism.injective,
    Subgroup.map_map, composite, Subgroup.map_id, inf_comm]

theorem invariant_le_intersection {group : Type*} [Group group]
    (automorphism : MulAut group) (subgroup invariant_group : Subgroup group)
    (contains : invariant_group ≤ subgroup)
    (invariant : invariant_group.map automorphism.toMonoidHom = invariant_group) :
    invariant_group ≤ intersection automorphism subgroup := by
  apply le_inf contains
  rw [← invariant]
  exact Subgroup.map_mono contains

theorem invariant_sylow_intersection_iff {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (automorphism : MulAut group)
    (involutive : Function.Involutive automorphism) (subgroup : Subgroup group)
    (odd_subgroup : Odd (Nat.card subgroup)) :
    primePart prime (Nat.card (intersection automorphism subgroup)) =
        primePart prime (Nat.card subgroup) ↔
      ∃ sylow : Sylow prime subgroup,
        ((sylow : Subgroup subgroup).map subgroup.subtype).map automorphism.toMonoidHom =
          (sylow : Subgroup subgroup).map subgroup.subtype := by
  constructor
  · intro equal_parts
    let common := intersection automorphism subgroup
    have common_invariant := intersection_invariant automorphism involutive subgroup
    have common_odd : Odd (Nat.card common) :=
      odd_subgroup.of_dvd_nat (Subgroup.card_dvd_of_le (show common ≤ subgroup from inf_le_left))
    let restricted := CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism automorphism common
      common_invariant
    obtain ⟨internal, internal_invariant⟩ :=
      CFSG.OrderReductions.InvariantSylow.exists_invariant_sylow_of_odd prime common_odd restricted
        (CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism_involutive automorphism involutive
          common common_invariant)
    let image := (internal : Subgroup common).map common.subtype
    have image_card : Nat.card image = primePart prime (Nat.card subgroup) :=
      (sylow_map_card_eq_primePart prime common internal).trans equal_parts
    have image_le : image ≤ subgroup := by
      intro element mem_image
      obtain ⟨original, _, equal_image⟩ := Subgroup.mem_map.mp mem_image
      exact equal_image ▸ original.property.1
    obtain ⟨sylow, equal_image⟩ := exists_sylow_image_of_card prime image subgroup image_le image_card
    refine ⟨sylow, ?_⟩
    rw [equal_image]
    exact CFSG.OrderReductions.InvariantSylow.map_subtype_invariant automorphism common common_invariant
      internal internal_invariant
  · rintro ⟨sylow, invariant⟩
    apply (primePart_eq_iff_contains_sylow prime (intersection automorphism subgroup)
      subgroup inf_le_left).mpr
    refine ⟨sylow, ?_⟩
    apply invariant_le_intersection automorphism subgroup
      ((sylow : Subgroup subgroup).map subgroup.subtype) ?_ invariant
    intro element mem_image
    obtain ⟨original, _, equal_image⟩ := Subgroup.mem_map.mp mem_image
    exact equal_image ▸ original.property

theorem cyclic_automorphism_fixedSubgroup {group : Type*} [Group group]
    (automorphism : MulAut group) :
    CFSG.OrderReductions.CoprimeFixedSubgroup.fixedSubgroup (Subgroup.zpowers automorphism).subtype =
      CFSG.OrderReductions.OddInversion.fixedSubgroup automorphism := by
  ext element
  rw [CFSG.OrderReductions.CoprimeFixedSubgroup.mem_fixedSubgroup]
  change (∀ acting : Subgroup.zpowers automorphism, acting.val element = element) ↔
    automorphism element = element
  constructor
  · intro fixed
    exact fixed ⟨automorphism, Subgroup.mem_zpowers automorphism⟩
  · intro fixed
    have contains : Subgroup.zpowers automorphism ≤ MulAction.stabilizer (MulAut group) element :=
      Subgroup.zpowers_le.mpr fixed
    intro acting
    exact contains acting.property

theorem cyclic_automorphism_two_group {group : Type*} [Group group]
    (automorphism : MulAut group) (involutive : Function.Involutive automorphism) :
    IsPGroup 2 (Subgroup.zpowers automorphism) := by
  have square_one : automorphism ^ 2 = 1 := by
    ext element
    exact involutive element
  apply IsPGroup.of_card_dvd_pow (n := 1)
  rw [Nat.card_zpowers, pow_one]
  exact orderOf_dvd_of_pow_eq_one square_one

theorem sylow_fixed_card_of_odd {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (odd_group : Odd (Nat.card group))
    (automorphism : MulAut group) (involutive : Function.Involutive automorphism)
    (sylow : Sylow prime group)
    (invariant : (sylow : Subgroup group).map automorphism.toMonoidHom = sylow) :
    Nat.card ↥((sylow : Subgroup group) ⊓ CFSG.OrderReductions.OddInversion.fixedSubgroup automorphism) =
      primePart prime (Nat.card (CFSG.OrderReductions.OddInversion.fixedSubgroup automorphism)) := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  have invariant_all : ∀ acting : Subgroup.zpowers automorphism,
      (sylow : Subgroup group).map acting.val.toMonoidHom = sylow := by
    have fixes : automorphism • (sylow : Subgroup group) = (sylow : Subgroup group) := invariant
    have contains : Subgroup.zpowers automorphism ≤
        MulAction.stabilizer (MulAut group) (sylow : Subgroup group) :=
      Subgroup.zpowers_le.mpr fixes
    intro acting
    exact contains acting.property
  have card_eq := CFSG.OrderReductions.CoprimeFixedSubgroup.sylow_fixed_intersection_card
    2 prime (cyclic_automorphism_two_group automorphism involutive) odd_group.not_two_dvd_nat
      (Subgroup.zpowers automorphism).subtype sylow invariant_all
  rw [cyclic_automorphism_fixedSubgroup] at card_eq
  exact card_eq

theorem fixed_intersection_le {group : Type*} [Group group]
    (automorphism : MulAut group) (subgroup : Subgroup group) :
    subgroup ⊓ CFSG.OrderReductions.OddInversion.fixedSubgroup automorphism ≤
      intersection automorphism subgroup := by
  intro element mem_fixed
  refine ⟨mem_fixed.1, ?_⟩
  have fixed : automorphism element = element := mem_fixed.2
  exact Subgroup.mem_map.mpr ⟨element, mem_fixed.1, fixed⟩

theorem fixed_intersection_eq {group : Type*} [Group group]
    (automorphism : MulAut group) (subgroup : Subgroup group) :
    intersection automorphism subgroup ⊓ CFSG.OrderReductions.OddInversion.fixedSubgroup automorphism =
      subgroup ⊓ CFSG.OrderReductions.OddInversion.fixedSubgroup automorphism := by
  apply le_antisymm
  · exact inf_le_inf_right _ inf_le_left
  · exact le_inf (fixed_intersection_le automorphism subgroup) inf_le_right

theorem restricted_fixed_image {group : Type*} [Group group]
    (automorphism : MulAut group) (subgroup : Subgroup group)
    (invariant : subgroup.map automorphism.toMonoidHom = subgroup) :
    (CFSG.OrderReductions.OddInversion.fixedSubgroup
      (CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism automorphism subgroup invariant)).map
        subgroup.subtype = subgroup ⊓ CFSG.OrderReductions.OddInversion.fixedSubgroup automorphism := by
  ext element
  constructor
  · intro mem_image
    obtain ⟨original, original_fixed, equal_image⟩ := Subgroup.mem_map.mp mem_image
    rw [← equal_image]
    refine ⟨original.property, ?_⟩
    exact congrArg Subtype.val original_fixed
  · intro mem_intersection
    refine Subgroup.mem_map.mpr ⟨⟨element, mem_intersection.1⟩, ?_, rfl⟩
    apply Subtype.ext
    exact mem_intersection.2

theorem invariant_intersection_fixed_card {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (automorphism : MulAut group)
    (involutive : Function.Involutive automorphism) (subgroup : Subgroup group)
    (odd_subgroup : Odd (Nat.card subgroup))
    (sylow : Sylow prime (intersection automorphism subgroup))
    (invariant :
      ((sylow : Subgroup (intersection automorphism subgroup)).map
        (intersection automorphism subgroup).subtype).map automorphism.toMonoidHom =
        (sylow : Subgroup (intersection automorphism subgroup)).map
          (intersection automorphism subgroup).subtype) :
    Nat.card ↥(((sylow : Subgroup (intersection automorphism subgroup)).map
      (intersection automorphism subgroup).subtype) ⊓
        CFSG.OrderReductions.OddInversion.fixedSubgroup automorphism) =
      primePart prime (Nat.card ↥(subgroup ⊓ CFSG.OrderReductions.OddInversion.fixedSubgroup automorphism)) := by
  let common := intersection automorphism subgroup
  have common_invariant := intersection_invariant automorphism involutive subgroup
  let restricted := CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism automorphism common
    common_invariant
  have internal_invariant : (sylow : Subgroup common).map restricted.toMonoidHom = sylow := by
    apply Subgroup.map_injective (f := common.subtype) Subtype.val_injective
    have intertwines : common.subtype.comp restricted.toMonoidHom =
        automorphism.toMonoidHom.comp common.subtype := by
      ext element
      rfl
    rw [Subgroup.map_map, intertwines, ← Subgroup.map_map]
    exact invariant
  have common_odd : Odd (Nat.card common) := odd_subgroup.of_dvd_nat
    (Subgroup.card_dvd_of_le (show common ≤ subgroup from inf_le_left))
  have card_eq := sylow_fixed_card_of_odd prime common_odd restricted
    (CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism_involutive automorphism involutive
      common common_invariant) sylow internal_invariant
  have fixed_image := restricted_fixed_image automorphism common common_invariant
  have intersection_image :
      ((sylow : Subgroup common) ⊓ CFSG.OrderReductions.OddInversion.fixedSubgroup restricted).map
        common.subtype =
      ((sylow : Subgroup common).map common.subtype) ⊓
        CFSG.OrderReductions.OddInversion.fixedSubgroup automorphism := by
    rw [Subgroup.map_inf _ _ _ Subtype.val_injective, fixed_image]
    apply le_antisymm
    · exact inf_le_inf_left _ inf_le_right
    · intro element mem_intersection
      obtain ⟨original, _, equal_image⟩ := Subgroup.mem_map.mp mem_intersection.1
      exact ⟨mem_intersection.1, equal_image ▸ original.property, mem_intersection.2⟩
  have internal_card : Nat.card ↥((sylow : Subgroup common) ⊓
      CFSG.OrderReductions.OddInversion.fixedSubgroup restricted) =
      Nat.card ↥(((sylow : Subgroup common).map common.subtype) ⊓
        CFSG.OrderReductions.OddInversion.fixedSubgroup automorphism) := by
    rw [← intersection_image, Subgroup.card_map_of_injective Subtype.val_injective]
  rw [internal_card] at card_eq
  have common_fixed_card : Nat.card (CFSG.OrderReductions.OddInversion.fixedSubgroup restricted) =
      Nat.card ↥(subgroup ⊓ CFSG.OrderReductions.OddInversion.fixedSubgroup automorphism) := by
    rw [← Subgroup.card_map_of_injective (K := CFSG.OrderReductions.OddInversion.fixedSubgroup restricted)
      (f := common.subtype) Subtype.val_injective, fixed_image]
    change Nat.card ↥(intersection automorphism subgroup ⊓
      CFSG.OrderReductions.OddInversion.fixedSubgroup automorphism) = _
    rw [fixed_intersection_eq]
  rw [common_fixed_card] at card_eq
  exact card_eq

end CFSG.OrderReductions.InvolutiveIntersection
