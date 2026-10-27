module

public import CFSG.Assembly.OrderReductions.EmptyRegularity

public section

namespace CFSG.OrderReductions.PointMaximal

open CFSG.OrderReductions.InvolutionGraph
open CFSG.OrderReductions.TwoPointInvolutions

@[expose] def PointThreePointPrime {group : Type*} [Group group] (prime : ℕ) (point : Component group)
    (subgroup : Subgroup group) : Prop :=
  CFSG.OrderReductions.MaximalThreePoint.ThreePointPrime (points := Component group) prime subgroup ∧
    subgroup ≤ componentStabilizer point

theorem no_fixed_two_of_regular {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (odd_prime : Odd prime)
    (even_point_rule : CFSG.OrderReductions.EmptyRegularity.EvenPointRule (group := group) prime)
    (first second : Component group) (distinct : first ≠ second)
    (regular : CFSG.OrderReductions.PrimeRegular.PRegular prime (pairSubgroup first second) (componentStabilizer first))
    (subgroup : Subgroup group) (prime_group : IsPGroup prime subgroup) :
    Nat.card (MulAction.fixedPoints subgroup (Component group)) ≠ 2 := by
  intro fixed_two
  exact CFSG.OrderReductions.EmptyRegularity.no_regular_of_fixed_pair prime odd_prime even_point_rule
    subgroup prime_group fixed_two first second distinct regular

theorem point_maximal_global_of_no_fixed_two {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (point : Component group)
    (subgroup : Subgroup group) (maximal : Maximal (PointThreePointPrime prime point) subgroup)
    (no_two : ∀ prime_subgroup : Subgroup group, IsPGroup prime prime_subgroup →
      Nat.card (MulAction.fixedPoints prime_subgroup (Component group)) ≠ 2) :
    Maximal (CFSG.OrderReductions.MaximalThreePoint.ThreePointPrime (points := Component group) prime) subgroup ∧
      ∃ other : Component group, point ≠ other ∧
        ∃ sylow : Sylow prime (pairSubgroup point other),
          (sylow : Subgroup (pairSubgroup point other)).map (pairSubgroup point other).subtype = subgroup := by
  classical
  obtain ⟨global, subgroup_le_global, global_maximal⟩ := Finite.exists_le_maximal maximal.prop.1
  have global_fixed_large : 1 < (MulAction.fixedPoints global (Component group)).ncard := by
    rw [← Nat.card_coe_set_eq]
    exact lt_of_lt_of_le (by decide : 1 < 3) global_maximal.prop.2
  obtain ⟨first, first_fixed, second, second_fixed, distinct⟩ :=
    (Set.one_lt_ncard (Set.toFinite _)).mp global_fixed_large
  have other_exists : ∃ other ∈ MulAction.fixedPoints global (Component group), point ≠ other := by
    by_cases first_eq : first = point
    · exact ⟨second, second_fixed, fun equal => distinct (first_eq.trans equal)⟩
    · exact ⟨first, first_fixed, Ne.symm first_eq⟩
  obtain ⟨other, other_fixed, point_distinct⟩ := other_exists
  have global_le_other : global ≤ componentStabilizer other := by
    intro element element_mem
    exact MulAction.mem_fixedPoints.mp other_fixed ⟨element, element_mem⟩
  have subgroup_le_pair : subgroup ≤ pairSubgroup point other :=
    le_inf maximal.prop.2 (subgroup_le_global.trans global_le_other)
  have internal_prime : IsPGroup prime (subgroup.subgroupOf (pairSubgroup point other)) :=
    maximal.prop.1.1.of_equiv (Subgroup.subgroupOfEquivOfLe subgroup_le_pair).symm
  obtain ⟨sylow, internal_contains⟩ := internal_prime.exists_le_sylow
  let image := (sylow : Subgroup (pairSubgroup point other)).map (pairSubgroup point other).subtype
  have image_prime : IsPGroup prime image := sylow.isPGroup'.map _
  have subgroup_le_image : subgroup ≤ image := by
    rw [← Subgroup.map_subgroupOf_eq_of_le subgroup_le_pair]
    exact Subgroup.map_mono internal_contains
  have image_pair : image ≤ pairSubgroup point other := Subgroup.map_subtype_le _
  have point_fixed : point ∈ MulAction.fixedPoints image (Component group) :=
    MulAction.mem_fixedPoints.mpr fun element => (image_pair element.property).1
  have image_other_fixed : other ∈ MulAction.fixedPoints image (Component group) :=
    MulAction.mem_fixedPoints.mpr fun element => (image_pair element.property).2
  have image_three : CFSG.OrderReductions.MaximalThreePoint.ThreePointPrime (points := Component group) prime image := by
    refine ⟨image_prime, ?_⟩
    by_contra not_three
    have fixed_pair := CFSG.OrderReductions.MaximalThreePoint.fixedPoints_le_two_eq_pair image point other point_distinct
      point_fixed image_other_fixed (by omega)
    have fixed_two : Nat.card (MulAction.fixedPoints image (Component group)) = 2 := by
      rw [fixed_pair, Nat.card_coe_set_eq, Set.ncard_pair point_distinct]
    exact no_two image image_prime fixed_two
  have image_eq : image = subgroup :=
    (maximal.eq_of_le ⟨image_three, image_pair.trans inf_le_left⟩ subgroup_le_image).symm
  obtain ⟨flip, flip_normalizes, point_moves, other_moves⟩ :=
    CFSG.OrderReductions.TwoPointSylow.exists_sylow_normalizing_flip prime point other point_distinct sylow
  change flip.val ∈ Subgroup.normalizer (image : Set group) at flip_normalizes
  rw [image_eq] at flip_normalizes
  have subgroup_invariant : subgroup.map (MulAut.conj flip.val).toMonoidHom = subgroup :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp flip_normalizes
  have global_image_prime := global_maximal.prop.1.map (MulAut.conj flip.val).toMonoidHom
  have global_image_three : CFSG.OrderReductions.MaximalThreePoint.ThreePointPrime (points := Component group) prime
      (global.map (MulAut.conj flip.val).toMonoidHom) := by
    refine ⟨global_image_prime, ?_⟩
    have fixed_card : Nat.card (MulAction.fixedPoints (global.map (MulAut.conj flip.val).toMonoidHom)
        (Component group)) = Nat.card (MulAction.fixedPoints global (Component group)) := by
      let equivalence : MulAction.fixedPoints global (Component group) ≃
          MulAction.fixedPoints (global.map (MulAut.conj flip.val).toMonoidHom) (Component group) :=
        { toFun := fun fixed => ⟨flip.val • fixed.val,
            CFSG.OrderReductions.FixedPairSylow.conjugate_smul_mem_fixedPoints global flip.val fixed.property⟩
          invFun := fun fixed => ⟨flip.val⁻¹ • fixed.val, by
            have transported := CFSG.OrderReductions.FixedPairSylow.conjugate_smul_mem_fixedPoints
              (global.map (MulAut.conj flip.val).toMonoidHom) flip.val⁻¹ fixed.property
            have composite : (MulAut.conj flip.val⁻¹).toMonoidHom.comp
                (MulAut.conj flip.val).toMonoidHom = MonoidHom.id group := by
              ext element
              change flip.val⁻¹ * (flip.val * element * flip.val⁻¹) * (flip.val⁻¹)⁻¹ = element
              group
            rw [Subgroup.map_map, composite, Subgroup.map_id] at transported
            exact transported⟩
          left_inv := fun _ => Subtype.ext (inv_smul_smul _ _)
          right_inv := fun _ => Subtype.ext (smul_inv_smul _ _) }
      exact (Nat.card_congr equivalence).symm
    rw [fixed_card]
    exact global_maximal.prop.2
  have global_image_point : global.map (MulAut.conj flip.val).toMonoidHom ≤ componentStabilizer point := by
    have image_le := Subgroup.map_mono (f := (MulAut.conj flip.val).toMonoidHom) global_le_other
    rwa [← componentStabilizer_smul, other_moves] at image_le
  have subgroup_le_global_image : subgroup ≤ global.map (MulAut.conj flip.val).toMonoidHom := by
    rw [← subgroup_invariant]
    exact Subgroup.map_mono subgroup_le_global
  have global_image_eq := maximal.eq_of_le ⟨global_image_three, global_image_point⟩ subgroup_le_global_image
  have global_card : Nat.card global = Nat.card subgroup := by
    rw [global_image_eq, Subgroup.card_map_of_injective (MulAut.conj flip.val).injective]
  have global_eq := Subgroup.eq_of_le_of_card_ge subgroup_le_global global_card.le
  refine ⟨global_eq ▸ global_maximal, other, point_distinct, sylow, image_eq⟩

theorem point_maximal_even_of_no_fixed_two {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)]
    (even_point_rule : CFSG.OrderReductions.EmptyRegularity.EvenPointRule (group := group) prime)
    (point : Component group) (subgroup : Subgroup group)
    (maximal : Maximal (PointThreePointPrime prime point) subgroup)
    (no_two : ∀ prime_subgroup : Subgroup group, IsPGroup prime prime_subgroup →
      Nat.card (MulAction.fixedPoints prime_subgroup (Component group)) ≠ 2) :
    Even (Nat.card ↥(Subgroup.normalizer (subgroup : Set group) ⊓ componentStabilizer point)) := by
  obtain ⟨global_maximal, other, distinct, sylow, image_eq⟩ :=
    point_maximal_global_of_no_fixed_two prime point subgroup maximal no_two
  obtain ⟨base, base_fixed, base_even⟩ := even_point_rule subgroup global_maximal
  apply CFSG.OrderReductions.LocalRegularity.maximal_all_point_normalizers_even prime subgroup global_maximal
    point other distinct sylow (image_eq ▸ le_rfl) base base_fixed base_even point
  exact MulAction.mem_fixedPoints.mpr fun element => maximal.prop.2 element.property

end CFSG.OrderReductions.PointMaximal
