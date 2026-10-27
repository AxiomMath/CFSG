module

public import CFSG.Assembly.OrderReductions.NormalizerSylow
public import CFSG.Assembly.OrderReductions.PointMaximal

public section

namespace CFSG.OrderReductions.NormalizerTerminal

open CFSG.OrderReductions.InvolutionGraph
open CFSG.OrderReductions.TwoPointInvolutions

theorem internal_sylow_excludes_three_fixed {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)]
    (even_point_rule : CFSG.OrderReductions.EmptyRegularity.EvenPointRule (group := group) prime)
    (point : Component group) (normalizer : Subgroup group)
    (all_normalize : ∀ involution : Involution group,
      involution.val ∈ componentStabilizer point → involution.val ∈ normalizer)
    (ambient : Sylow prime normalizer) (image : Subgroup group)
    (image_eq : (ambient : Subgroup normalizer).map normalizer.subtype = image)
    (image_point : image ≤ componentStabilizer point)
    (odd_normalizer : Odd (Nat.card ↥(Subgroup.normalizer (image : Set group) ⊓ componentStabilizer point)))
    (no_two : ∀ prime_subgroup : Subgroup group, IsPGroup prime prime_subgroup →
      Nat.card (MulAction.fixedPoints prime_subgroup (Component group)) ≠ 2) :
    ¬ 3 ≤ Nat.card (MulAction.fixedPoints image (Component group)) := by
  classical
  intro three_fixed
  have image_prime : IsPGroup prime image := image_eq ▸ ambient.isPGroup'.map normalizer.subtype
  have image_three : CFSG.OrderReductions.PointMaximal.PointThreePointPrime prime point image :=
    ⟨⟨image_prime, three_fixed⟩, image_point⟩
  obtain ⟨maximal_group, image_le, maximal⟩ := Finite.exists_le_maximal image_three
  have even_normalizer := CFSG.OrderReductions.PointMaximal.point_maximal_even_of_no_fixed_two
    prime even_point_rule point maximal_group maximal no_two
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨element, element_order⟩ := exists_prime_orderOf_dvd_card' 2 even_normalizer.two_dvd
  let involution : Involution group :=
    ⟨element.val, (Subgroup.orderOf_coe element).trans element_order⟩
  have mem_point : involution.val ∈ componentStabilizer point := element.property.2
  have mem_normalizer : involution.val ∈ normalizer := all_normalize involution mem_point
  have normalizes : involution.val ∈ Subgroup.normalizer (maximal_group : Set group) := element.property.1
  have internal_prime : IsPGroup prime (maximal_group.subgroupOf normalizer) :=
    maximal.prop.1.1.comap_of_injective normalizer.subtype Subtype.val_injective
  have ambient_le : (ambient : Subgroup normalizer) ≤ maximal_group.subgroupOf normalizer := by
    intro original original_mem
    apply image_le
    rw [← image_eq]
    exact Subgroup.mem_map_of_mem normalizer.subtype original_mem
  have equal_internal := ambient.is_maximal' internal_prime ambient_le
  have intersection_eq : maximal_group ⊓ normalizer = image := by
    rw [← Subgroup.subgroupOf_map_subtype, equal_internal]
    exact image_eq
  have maximal_invariant : maximal_group.map (MulAut.conj involution.val).toMonoidHom = maximal_group :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp normalizes
  have normalizer_invariant : normalizer.map (MulAut.conj involution.val).toMonoidHom = normalizer :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (normalizer.le_normalizer mem_normalizer)
  have image_invariant : image.map (MulAut.conj involution.val).toMonoidHom = image := by
    rw [← intersection_eq, Subgroup.map_inf _ _ _ (MulAut.conj involution.val).injective,
      maximal_invariant, normalizer_invariant]
  have image_normalizes : involution.val ∈ Subgroup.normalizer (image : Set group) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr image_invariant
  have divides := Subgroup.orderOf_dvd_natCard
    (Subgroup.normalizer (image : Set group) ⊓ componentStabilizer point) ⟨image_normalizes, mem_point⟩
  rw [involution.property] at divides
  exact odd_normalizer.not_two_dvd_nat divides

theorem double_transitive_of_normalizer_sylow {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (odd_prime : Odd prime)
    (even_point_rule : CFSG.OrderReductions.EmptyRegularity.EvenPointRule (group := group) prime)
    (point other : Component group) (distinct : point ≠ other) (degree : 3 ≤ Nat.card (Component group))
    (normalizer : Subgroup group)
    (all_normalize : ∀ involution : Involution group,
      involution.val ∈ componentStabilizer point → involution.val ∈ normalizer)
    (sylow : Sylow prime (pairSubgroup point other))
    (ambient : Sylow prime normalizer)
    (image_eq : (ambient : Subgroup normalizer).map normalizer.subtype =
      (sylow : Subgroup (pairSubgroup point other)).map (pairSubgroup point other).subtype)
    (not_regular : ¬ CFSG.OrderReductions.PrimeRegular.PRegular prime (pairSubgroup point other) (componentStabilizer point)) :
    MulAction.IsMultiplyPretransitive group (Component group) 2 := by
  classical
  by_cases no_regular : CFSG.OrderReductions.EmptyRegularity.NoRegularPair (group := group) prime
  · exact CFSG.OrderReductions.EmptyRegularity.no_regular_double_transitive prime even_point_rule no_regular degree
  · have regular_exists : ∃ first second : Component group, first ≠ second ∧
        CFSG.OrderReductions.PrimeRegular.PRegular prime (pairSubgroup first second) (componentStabilizer first) := by
      by_contra missing
      apply no_regular
      intro first second other_distinct regular
      exact missing ⟨first, second, other_distinct, regular⟩
    obtain ⟨first, second, other_distinct, regular⟩ := regular_exists
    have no_two := CFSG.OrderReductions.PointMaximal.no_fixed_two_of_regular prime odd_prime even_point_rule
      first second other_distinct regular
    let image := (sylow : Subgroup (pairSubgroup point other)).map (pairSubgroup point other).subtype
    have image_prime : IsPGroup prime image := sylow.isPGroup'.map _
    have image_pair : image ≤ pairSubgroup point other := Subgroup.map_subtype_le _
    have first_fixed : point ∈ MulAction.fixedPoints image (Component group) :=
      MulAction.mem_fixedPoints.mpr fun element => (image_pair element.property).1
    have second_fixed : other ∈ MulAction.fixedPoints image (Component group) :=
      MulAction.mem_fixedPoints.mpr fun element => (image_pair element.property).2
    have odd_normalizer := CFSG.OrderReductions.NormalizerSylow.odd_sylow_point_normalizer_of_nonregular
      prime point other distinct not_regular sylow
    have not_three := internal_sylow_excludes_three_fixed prime even_point_rule point normalizer all_normalize
      ambient image image_eq (image_pair.trans inf_le_left) odd_normalizer no_two
    have fixed_pair := CFSG.OrderReductions.MaximalThreePoint.fixedPoints_le_two_eq_pair image point other distinct
      first_fixed second_fixed (by omega)
    have fixed_two : Nat.card (MulAction.fixedPoints image (Component group)) = 2 := by
      rw [fixed_pair, Nat.card_coe_set_eq, Set.ncard_pair distinct]
    exact False.elim (no_two image image_prime fixed_two)

end CFSG.OrderReductions.NormalizerTerminal
