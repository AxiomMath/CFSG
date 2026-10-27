module

public import CFSG.Assembly.OrderReductions.OddPrimeCoreTransfer
public import CFSG.Assembly.OrderReductions.EmptyRegularity

public section

namespace CFSG.OrderReductions.NormalizerAuxiliary

open CFSG.OrderReductions.InvolutionGraph
open CFSG.OrderReductions.PrimeComplementCore

@[expose] def inversionSet {group : Type*} [Group group]
    (subgroup : Subgroup group) (involution : Involution group) : Set group :=
  {element | element ∈ subgroup ∧ (MulAut.conj involution.val) element = element⁻¹}

theorem conjugator_in_normalizer {group : Type*} [Group group] [Finite group]
    (ambient : Subgroup group) (strong : StronglyEmbedded ambient)
    (subgroup : Subgroup group) (first second : Involution group)
    (first_mem : first.val ∈ ambient) (second_not_mem : second.val ∉ ambient)
    (first_normalizes : first.val ∈ Subgroup.normalizer (subgroup : Set group))
    (second_normalizes : second.val ∈ Subgroup.normalizer (subgroup : Set group)) :
    ∃ conjugator : Involution group,
      conjugator.val ∈ Subgroup.normalizer (subgroup : Set group) ∧
        conjugator.val • first = second := by
  let normalizer := Subgroup.normalizer (subgroup : Set group)
  let internal_first : Involution normalizer :=
    ⟨⟨first.val, first_normalizes⟩, by rw [← Subgroup.orderOf_coe]; exact first.property⟩
  let internal_second : Involution normalizer :=
    ⟨⟨second.val, second_normalizes⟩, by rw [← Subgroup.orderOf_coe]; exact second.property⟩
  have not_reachable : ¬ (commutingGraph group).Reachable first second :=
    fun reachable => second_not_mem
      (stronglyEmbedded_reachable_mem ambient strong first second first_mem reachable)
  have odd_product := CFSG.OrderReductions.InvolutionFusion.odd_product_order_of_not_reachable
    first second not_reachable
  have internal_odd : Odd (orderOf (internal_first.val * internal_second.val)) := by
    exact (Subgroup.orderOf_coe (internal_first.val * internal_second.val)) ▸ odd_product
  have internal_distinct : internal_first ≠ internal_second := by
    intro equal_internal
    exact second_not_mem ((congrArg (fun current : Involution normalizer => current.val.val)
      equal_internal) ▸ first_mem)
  obtain ⟨internal_conjugator, conjugates⟩ :=
    CFSG.OrderReductions.InvolutionFusion.involution_conjugator_of_odd_product_order
      internal_first internal_second internal_distinct internal_odd
  let conjugator : Involution group :=
    ⟨internal_conjugator.val.val, (Subgroup.orderOf_coe internal_conjugator.val).trans
      internal_conjugator.property⟩
  refine ⟨conjugator, internal_conjugator.val.property, ?_⟩
  apply Subtype.ext
  exact congrArg (fun current : Involution normalizer => current.val.val) conjugates

theorem component_smul_of_conjugates {group : Type*} [Group group] [Finite group]
    (point : Component group) (first second : Involution group)
    (first_mem : first.val ∈ componentStabilizer point) (element : group)
    (conjugates : element • first = second) :
    element • point = (commutingGraph group).connectedComponentMk second := by
  rw [← (componentStabilizer_involution_iff point first).mp first_mem,
    componentMk_smul, conjugates]

theorem prime_le_involution_point_of_normalizes {group : Type*} [Group group] [Finite group]
    (point : Component group) (strong : StronglyEmbedded (componentStabilizer point))
    (subgroup : Subgroup group) (contains : subgroup ≤ componentStabilizer point)
    (first second : Involution group) (first_mem : first.val ∈ componentStabilizer point)
    (second_not_mem : second.val ∉ componentStabilizer point)
    (first_normalizes : first.val ∈ Subgroup.normalizer (subgroup : Set group))
    (second_normalizes : second.val ∈ Subgroup.normalizer (subgroup : Set group)) :
    subgroup ≤ componentStabilizer ((commutingGraph group).connectedComponentMk second) := by
  obtain ⟨conjugator, normalizes, conjugates⟩ := conjugator_in_normalizer
    (componentStabilizer point) strong subgroup first second first_mem second_not_mem
      first_normalizes second_normalizes
  have image_le := Subgroup.map_mono (f := (MulAut.conj conjugator.val).toMonoidHom) contains
  have invariant : subgroup.map (MulAut.conj conjugator.val).toMonoidHom = subgroup :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp normalizes
  rw [invariant, ← componentStabilizer_smul,
    component_smul_of_conjugates point first second first_mem conjugator.val conjugates] at image_le
  exact image_le

theorem centralizer_image_eq {source target : Type*} [Group source] [Group target]
    (equivalence : source ≃* target) (elements : Set source) :
    Subgroup.centralizer (equivalence '' elements) =
      (Subgroup.centralizer elements).map equivalence.toMonoidHom := by
  apply le_antisymm
  · intro element centralizes
    apply Subgroup.mem_map.mpr
    refine ⟨equivalence.symm element, Subgroup.mem_centralizer_iff.mpr ?_,
      equivalence.apply_symm_apply element⟩
    intro other other_mem
    apply equivalence.injective
    simpa only [map_mul, equivalence.apply_symm_apply] using
      Subgroup.mem_centralizer_iff.mp centralizes (equivalence other) ⟨other, other_mem, rfl⟩
  · exact Subgroup.map_centralizer_le_centralizer_image elements equivalence.toMonoidHom

theorem conjugation_intertwines {group : Type*} [Group group]
    (first second : Involution group) (element : group) (conjugates : element • first = second) :
    (MulAut.conj second.val) * MulAut.conj element =
      MulAut.conj element * MulAut.conj first.val := by
  have conjugates_values : element * first.val * element⁻¹ = second.val :=
    congrArg Subtype.val conjugates
  have multiplied : second.val * element = element * first.val := by
    rw [← conjugates_values]
    group
  rw [← map_mul, ← map_mul, multiplied]

theorem contained_centralizer_core_transfer {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (point : Component group)
    (strong : StronglyEmbedded (componentStabilizer point))
    (prime_subgroup : Subgroup group) (prime_group : IsPGroup prime prime_subgroup)
    (contains : prime_subgroup ≤ componentStabilizer point)
    (first second : Involution group) (first_mem : first.val ∈ componentStabilizer point)
    (second_not_mem : second.val ∉ componentStabilizer point)
    (first_normalizes : first.val ∈ Subgroup.normalizer (prime_subgroup : Set group))
    (second_normalizes : second.val ∈ Subgroup.normalizer (prime_subgroup : Set group))
    (centralizer_le : Subgroup.centralizer (inversionSet prime_subgroup first) ≤
      componentStabilizer point) :
    inversionSet prime_subgroup first ⊆
      componentStabilizer ((commutingGraph group).connectedComponentMk second) ∧
    ambientCore prime (CFSG.OrderReductions.InvolutiveIntersection.intersection (MulAut.conj second.val)
      (componentStabilizer point)) ≤
        ambientCore prime (componentStabilizer ((commutingGraph group).connectedComponentMk second) ⊓
          CFSG.OrderReductions.InvolutiveIntersection.intersection (MulAut.conj second.val)
            (componentStabilizer point)) := by
  let second_point := (commutingGraph group).connectedComponentMk second
  have second_mem : second.val ∈ componentStabilizer second_point := involution_mem_componentStabilizer second
  have distinct : second_point ≠ point := by
    intro same
    exact second_not_mem (same ▸ second_mem)
  have prime_le_second := prime_le_involution_point_of_normalizes point strong prime_subgroup contains
    first second first_mem second_not_mem first_normalizes second_normalizes
  refine ⟨fun element element_mem => prime_le_second element_mem.1, ?_⟩
  obtain ⟨conjugator, normalizes, conjugates⟩ := conjugator_in_normalizer
    (componentStabilizer point) strong prime_subgroup first second first_mem second_not_mem
      first_normalizes second_normalizes
  let equivalence := MulAut.conj conjugator.val
  let elements := equivalence '' inversionSet prime_subgroup first
  let generated := Subgroup.closure elements
  have elements_le_prime : elements ⊆ prime_subgroup := by
    rintro element ⟨original, original_mem, image_eq⟩
    rw [← image_eq]
    exact (Subgroup.mem_normalizer_iff.mp normalizes original).mp original_mem.1
  have generated_le_prime : generated ≤ prime_subgroup := (Subgroup.closure_le _).mpr elements_le_prime
  have elements_inverted : ∀ element ∈ elements,
      (MulAut.conj second.val) element = element⁻¹ := by
    rintro element ⟨original, original_mem, image_eq⟩
    rw [← image_eq]
    have intertwines := congrArg (fun automorphism : MulAut group => automorphism original)
      (conjugation_intertwines first second conjugator.val conjugates)
    change (MulAut.conj second.val) (equivalence original) =
      equivalence ((MulAut.conj first.val) original) at intertwines
    rw [intertwines, original_mem.2, map_inv]
  have centralizer_image_le : Subgroup.centralizer elements ≤ componentStabilizer second_point := by
    rw [centralizer_image_eq]
    have image_le := Subgroup.map_mono (f := equivalence.toMonoidHom) centralizer_le
    rw [← componentStabilizer_smul,
      component_smul_of_conjugates point first second first_mem conjugator.val conjugates] at image_le
    exact image_le
  exact CFSG.OrderReductions.OddPrimeCoreTransfer.component_three_point_core_transfer prime second_point point distinct
    second second_mem elements generated rfl (prime_group.to_le generated_le_prime)
    (le_inf (generated_le_prime.trans prime_le_second) (generated_le_prime.trans contains))
    elements_inverted (inf_le_left.trans centralizer_image_le)

theorem normalizer_intersection_stronglyEmbedded {group : Type*} [Group group] [Finite group]
    (point : Component group) (strong : StronglyEmbedded (componentStabilizer point))
    (subgroup : Subgroup group) (involution : Involution group)
    (mem_point : involution.val ∈ componentStabilizer point)
    (normalizes : involution.val ∈ Subgroup.normalizer (subgroup : Set group))
    (crosses : ¬ Subgroup.normalizer (subgroup : Set group) ≤ componentStabilizer point) :
    StronglyEmbedded ((componentStabilizer point).subgroupOf
      (Subgroup.normalizer (subgroup : Set group))) := by
  apply CFSG.OrderReductions.StrongEmbeddingInheritance.intersection_stronglyEmbedded
    (componentStabilizer point) strong _ crosses
  apply even_iff_two_dvd.mpr
  have divides := Subgroup.orderOf_dvd_natCard
    (componentStabilizer point ⊓ Subgroup.normalizer (subgroup : Set group)) ⟨mem_point, normalizes⟩
  rwa [involution.property] at divides

@[expose] def AuxiliaryData {group : Type*} [Group group]
    (point : Component group) (elements : Set group) (involution : Involution group)
    (prime : ℕ) [Finite group] [Fact (Nat.Prime prime)] (subgroup : Subgroup group) : Prop :=
  involution.val ∈ subgroup ∧ StronglyEmbedded ((componentStabilizer point).subgroupOf subgroup) ∧
    ∀ outside : Involution group, outside.val ∈ subgroup → outside.val ∉ componentStabilizer point →
      elements ⊆ componentStabilizer ((commutingGraph group).connectedComponentMk outside) ∧
        ambientCore prime (CFSG.OrderReductions.InvolutiveIntersection.intersection (MulAut.conj outside.val)
          (componentStabilizer point)) ≤
            ambientCore prime (componentStabilizer ((commutingGraph group).connectedComponentMk outside) ⊓
              CFSG.OrderReductions.InvolutiveIntersection.intersection (MulAut.conj outside.val)
                (componentStabilizer point))

theorem normalizer_crosses_of_even_other_point {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (point other : Component group) (distinct : point ≠ other)
    (even_other : Even (Nat.card ↥(Subgroup.normalizer (subgroup : Set group) ⊓
      componentStabilizer other))) :
    ¬ Subgroup.normalizer (subgroup : Set group) ≤ componentStabilizer point := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨element, element_order⟩ := exists_prime_orderOf_dvd_card' 2 even_other.two_dvd
  let involution : Involution group :=
    ⟨element.val, (Subgroup.orderOf_coe element).trans element_order⟩
  intro contains
  exact distinct (CFSG.OrderReductions.MaximalThreePoint.involution_fixed_component_unique involution point other
    (contains element.property.1) element.property.2)

theorem normalizer_auxiliary_of_even_other {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (point other : Component group)
    (distinct : point ≠ other) (prime_subgroup : Subgroup group)
    (prime_group : IsPGroup prime prime_subgroup) (contains : prime_subgroup ≤ componentStabilizer point)
    (involution : Involution group) (mem_point : involution.val ∈ componentStabilizer point)
    (normalizes : involution.val ∈ Subgroup.normalizer (prime_subgroup : Set group))
    (even_other : Even (Nat.card ↥(Subgroup.normalizer (prime_subgroup : Set group) ⊓
      componentStabilizer other)))
    (centralizer_le : Subgroup.centralizer (inversionSet prime_subgroup involution) ≤
      componentStabilizer point) :
    AuxiliaryData point (inversionSet prime_subgroup involution) involution prime
      (Subgroup.normalizer (prime_subgroup : Set group)) := by
  have strong := componentStabilizer_stronglyEmbedded point ⟨other, distinct.symm⟩
  refine ⟨normalizes, normalizer_intersection_stronglyEmbedded point strong prime_subgroup
    involution mem_point normalizes
      (normalizer_crosses_of_even_other_point prime_subgroup point other distinct even_other), ?_⟩
  intro outside outside_normalizes outside_not_mem
  exact contained_centralizer_core_transfer prime point strong prime_subgroup prime_group contains
    involution outside mem_point outside_not_mem normalizes outside_normalizes centralizer_le

theorem maximal_contained_centralizer_auxiliary {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)]
    (even_point_rule : CFSG.OrderReductions.EmptyRegularity.EvenPointRule (group := group) prime)
    (prime_subgroup : Subgroup group)
    (maximal : Maximal (CFSG.OrderReductions.MaximalThreePoint.ThreePointPrime
      (points := Component group) prime) prime_subgroup)
    (initial_first initial_second : Component group) (initial_distinct : initial_first ≠ initial_second)
    (initial_sylow : Sylow prime (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup initial_first initial_second))
    (initial_contains : (initial_sylow :
      Subgroup (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup initial_first initial_second)).map
        (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup initial_first initial_second).subtype ≤ prime_subgroup)
    (point : Component group) (point_fixed : point ∈ MulAction.fixedPoints prime_subgroup (Component group))
    (involution : Involution group) (mem_point : involution.val ∈ componentStabilizer point)
    (normalizes : involution.val ∈ Subgroup.normalizer (prime_subgroup : Set group))
    (centralizer_le : Subgroup.centralizer (inversionSet prime_subgroup involution) ≤
      componentStabilizer point) :
    AuxiliaryData point (inversionSet prime_subgroup involution) involution prime
      (Subgroup.normalizer (prime_subgroup : Set group)) := by
  classical
  obtain ⟨base, base_fixed, base_even⟩ := even_point_rule prime_subgroup maximal
  have fixed_large : 1 < (MulAction.fixedPoints prime_subgroup (Component group)).ncard := by
    rw [← Nat.card_coe_set_eq]
    exact lt_of_lt_of_le (by decide : 1 < 3) maximal.prop.2
  obtain ⟨first, first_fixed, second, second_fixed, distinct⟩ :=
    (Set.one_lt_ncard (Set.toFinite _)).mp fixed_large
  have other_exists : ∃ other ∈ MulAction.fixedPoints prime_subgroup (Component group), other ≠ point := by
    by_cases first_eq : first = point
    · exact ⟨second, second_fixed, fun second_eq => distinct (first_eq.trans second_eq.symm)⟩
    · exact ⟨first, first_fixed, first_eq⟩
  obtain ⟨other, other_fixed, other_distinct⟩ := other_exists
  have even_other := CFSG.OrderReductions.LocalRegularity.maximal_all_point_normalizers_even prime
    prime_subgroup maximal initial_first initial_second initial_distinct initial_sylow initial_contains
    base base_fixed base_even other other_fixed
  apply normalizer_auxiliary_of_even_other prime point other other_distinct.symm prime_subgroup
    maximal.prop.1 _ involution mem_point normalizes even_other centralizer_le
  intro element element_mem
  exact MulAction.mem_fixedPoints.mp point_fixed ⟨element, element_mem⟩

end CFSG.OrderReductions.NormalizerAuxiliary
