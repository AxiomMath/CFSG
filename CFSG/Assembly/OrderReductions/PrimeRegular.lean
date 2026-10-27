module

public import CFSG.Assembly.OrderReductions.InvariantOrbitBound
public import CFSG.Assembly.OrderReductions.MaximalThreePoint

public section

namespace CFSG.OrderReductions.PrimeRegular

open CFSG.OrderReductions.InvolutionGraph
open CFSG.OrderReductions.PrimePart
open CFSG.OrderReductions.InvolutiveIntersection

@[expose] def PRegular {group : Type*} [Group group] (prime : ℕ)
    (subgroup ambient : Subgroup group) : Prop :=
  ∃ involution : Involution group, involution.val ∈ ambient ∧
    primePart prime (Nat.card (intersection (MulAut.conj involution.val) subgroup)) =
      primePart prime (Nat.card subgroup)

theorem involution_conjugation_involutive {group : Type*} [Group group]
    (involution : Involution group) : Function.Involutive (MulAut.conj involution.val) := by
  intro element
  change involution.val * (involution.val * element * involution.val⁻¹) * involution.val⁻¹ = element
  rw [inv_eq_self_of_orderOf_eq_two involution.property]
  have square_one := CFSG.OrderReductions.InvolutionFusion.involution_mul_self involution
  calc
    involution.val * (involution.val * element * involution.val) * involution.val =
        (involution.val * involution.val) * element * (involution.val * involution.val) := by group
    _ = element := by rw [square_one, one_mul, mul_one]

theorem involution_fixedSubgroup_eq_centralizer {group : Type*} [Group group]
    (involution : Involution group) :
    CFSG.OrderReductions.OddInversion.fixedSubgroup (MulAut.conj involution.val) =
      Subgroup.centralizer ({involution.val} : Set group) := by
  ext element
  rw [Subgroup.mem_centralizer_iff]
  change (MulAut.conj involution.val) element = element ↔
    ∀ other ∈ ({involution.val} : Set group), other * element = element * other
  constructor
  · intro fixed other mem_singleton
    have equal_other : other = involution.val := Set.mem_singleton_iff.mp mem_singleton
    subst other
    have multiplied := congrArg (fun current : group => current * involution.val) fixed
    simpa only [MulAut.conj_apply, mul_assoc, inv_mul_cancel, mul_one] using multiplied
  · intro commutes
    change involution.val * element * involution.val⁻¹ = element
    rw [commutes involution.val (by simp), mul_assoc, mul_inv_cancel, mul_one]

theorem involution_fixedIndex_eq_orbit_card {group : Type*} [Group group]
    (subgroup : Subgroup group) (involution : Involution group) :
    CFSG.OrderReductions.InvariantOrbitBound.fixedIndex (MulAut.conj involution.val) subgroup =
      Nat.card (MulAction.orbit subgroup involution) := by
  have stabilizer_eq : MulAction.stabilizer subgroup involution =
      (Subgroup.centralizer ({involution.val} : Set group)).subgroupOf subgroup := by
    ext element
    change element.val ∈ MulAction.stabilizer group involution ↔ _
    rw [involution_stabilizer_eq_centralizer]
    rfl
  unfold CFSG.OrderReductions.InvariantOrbitBound.fixedIndex
  rw [involution_fixedSubgroup_eq_centralizer]
  change ((Subgroup.centralizer ({involution.val} : Set group)).subgroupOf subgroup).index = _
  rw [← stabilizer_eq, MulAction.index_stabilizer, Nat.card_coe_set_eq]

theorem pRegular_iff_invariant_sylow {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (subgroup ambient : Subgroup group)
    (odd_subgroup : Odd (Nat.card subgroup)) :
    PRegular prime subgroup ambient ↔
      ∃ involution : Involution group, involution.val ∈ ambient ∧
        ∃ sylow : Sylow prime subgroup, involution.val ∈ Subgroup.normalizer
          ((sylow : Subgroup subgroup).map subgroup.subtype : Set group) := by
  constructor
  · rintro ⟨involution, mem_ambient, equal_parts⟩
    obtain ⟨sylow, invariant⟩ := (invariant_sylow_intersection_iff prime
      (MulAut.conj involution.val) (involution_conjugation_involutive involution) subgroup
        odd_subgroup).mp equal_parts
    exact ⟨involution, mem_ambient, sylow,
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr invariant⟩
  · rintro ⟨involution, mem_ambient, sylow, normalizes⟩
    refine ⟨involution, mem_ambient, ?_⟩
    apply (invariant_sylow_intersection_iff prime (MulAut.conj involution.val)
      (involution_conjugation_involutive involution) subgroup odd_subgroup).mpr
    exact ⟨sylow, Subgroup.mem_normalizer_iff_map_conj_eq.mp normalizes⟩

theorem pRegular_iff_some_even_normalizer {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (subgroup ambient : Subgroup group)
    (odd_subgroup : Odd (Nat.card subgroup)) :
    PRegular prime subgroup ambient ↔
      ∃ sylow : Sylow prime subgroup,
        Even (Nat.card ↥(Subgroup.normalizer
          ((sylow : Subgroup subgroup).map subgroup.subtype : Set group) ⊓ ambient)) := by
  rw [pRegular_iff_invariant_sylow prime subgroup ambient odd_subgroup]
  constructor
  · rintro ⟨involution, mem_ambient, sylow, normalizes⟩
    refine ⟨sylow, even_iff_two_dvd.mpr ?_⟩
    have divides := Subgroup.orderOf_dvd_natCard
      (Subgroup.normalizer ((sylow : Subgroup subgroup).map subgroup.subtype : Set group) ⊓ ambient)
        ⟨normalizes, mem_ambient⟩
    rwa [involution.property] at divides
  · rintro ⟨sylow, even_normalizer⟩
    have : Fact (Nat.Prime 2) := ⟨by decide⟩
    obtain ⟨element, element_order⟩ := exists_prime_orderOf_dvd_card' 2 even_normalizer.two_dvd
    let involution : Involution group :=
      ⟨element.val, (Subgroup.orderOf_coe element).trans element_order⟩
    exact ⟨involution, element.property.2, sylow, element.property.1⟩

theorem sylow_normalizer_card_eq {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (subgroup ambient : Subgroup group)
    (contains : subgroup ≤ ambient) (first second : Sylow prime subgroup) :
    Nat.card ↥(Subgroup.normalizer
      ((first : Subgroup subgroup).map subgroup.subtype : Set group) ⊓ ambient) =
    Nat.card ↥(Subgroup.normalizer
      ((second : Subgroup subgroup).map subgroup.subtype : Set group) ⊓ ambient) := by
  obtain ⟨conjugator, conjugates⟩ := MulAction.exists_smul_eq subgroup first second
  have conjugate_image := congrArg (fun current : Sylow prime subgroup =>
    (current : Subgroup subgroup).map subgroup.subtype) conjugates
  rw [CFSG.OrderReductions.FixedPairSylow.sylow_subtype_smul_image] at conjugate_image
  have ambient_invariant : ambient.map (MulAut.conj conjugator.val).toMonoidHom = ambient :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (ambient.le_normalizer (contains conjugator.property))
  have mapped : (Subgroup.normalizer
      ((first : Subgroup subgroup).map subgroup.subtype : Set group) ⊓ ambient).map
        (MulAut.conj conjugator.val).toMonoidHom =
      Subgroup.normalizer ((second : Subgroup subgroup).map subgroup.subtype : Set group) ⊓ ambient := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj conjugator.val).injective,
      Subgroup.map_normalizer_eq_of_bijective _ (MulAut.conj conjugator.val).bijective,
      conjugate_image, ambient_invariant]
  rw [← mapped, Subgroup.card_map_of_injective (MulAut.conj conjugator.val).injective]

theorem pRegular_iff_every_even_normalizer {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (subgroup ambient : Subgroup group)
    (contains : subgroup ≤ ambient) (odd_subgroup : Odd (Nat.card subgroup)) :
    PRegular prime subgroup ambient ↔
      ∀ sylow : Sylow prime subgroup,
        Even (Nat.card ↥(Subgroup.normalizer
          ((sylow : Subgroup subgroup).map subgroup.subtype : Set group) ⊓ ambient)) := by
  rw [pRegular_iff_some_even_normalizer prime subgroup ambient odd_subgroup]
  constructor
  · rintro ⟨sample, even_sample⟩ sylow
    rw [← sylow_normalizer_card_eq prime subgroup ambient contains sample sylow]
    exact even_sample
  · intro all_even
    obtain ⟨sylow⟩ := Sylow.nonempty (p := prime) (G := subgroup)
    exact ⟨sylow, all_even sylow⟩

theorem pRegular_iff_prime_orbit_large {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (subgroup ambient : Subgroup group)
    (odd_subgroup : Odd (Nat.card subgroup)) :
    PRegular prime subgroup ambient ↔
      ∃ involution : Involution group, involution.val ∈ ambient ∧
        ∃ prime_subgroup : Subgroup group, IsPGroup prime prime_subgroup ∧
          prime_subgroup ≤ subgroup ∧
          involution.val ∈ Subgroup.normalizer (prime_subgroup : Set group) ∧
          primePart prime (Nat.card (MulAction.orbit subgroup involution)) ≤
            Nat.card (MulAction.orbit prime_subgroup involution) := by
  rw [pRegular_iff_invariant_sylow prime subgroup ambient odd_subgroup]
  constructor
  · rintro ⟨involution, mem_ambient, sylow, normalizes⟩
    have invariant : ((sylow : Subgroup subgroup).map subgroup.subtype).map
        (MulAut.conj involution.val).toMonoidHom =
        (sylow : Subgroup subgroup).map subgroup.subtype :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp normalizes
    have criterion := (CFSG.OrderReductions.InvariantOrbitBound.invariant_prime_index_criterion prime
      (MulAut.conj involution.val) (involution_conjugation_involutive involution) subgroup
        odd_subgroup).mp ⟨sylow, invariant⟩
    obtain ⟨prime_subgroup, prime_group, contains, prime_invariant, large⟩ := criterion
    refine ⟨involution, mem_ambient, prime_subgroup, prime_group, contains,
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr prime_invariant, ?_⟩
    rwa [involution_fixedIndex_eq_orbit_card, involution_fixedIndex_eq_orbit_card] at large
  · rintro ⟨involution, mem_ambient, prime_subgroup, prime_group, contains, normalizes, large⟩
    have index_large : primePart prime
        (CFSG.OrderReductions.InvariantOrbitBound.fixedIndex (MulAut.conj involution.val) subgroup) ≤
        CFSG.OrderReductions.InvariantOrbitBound.fixedIndex (MulAut.conj involution.val) prime_subgroup := by
      rwa [involution_fixedIndex_eq_orbit_card, involution_fixedIndex_eq_orbit_card]
    obtain ⟨sylow, invariant⟩ := (CFSG.OrderReductions.InvariantOrbitBound.invariant_prime_index_criterion
      prime (MulAut.conj involution.val) (involution_conjugation_involutive involution)
        subgroup odd_subgroup).mpr ⟨prime_subgroup, prime_group, contains,
          Subgroup.mem_normalizer_iff_map_conj_eq.mp normalizes, index_large⟩
    exact ⟨involution, mem_ambient, sylow,
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr invariant⟩

theorem pair_involution_orbit_card {group : Type*} [Group group] [Finite group]
    (first second : Component group) (distinct : first ≠ second)
    (involution : Involution group) (mem_first : involution.val ∈ componentStabilizer first) :
    Nat.card (MulAction.orbit (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second) involution) =
      Nat.card (Involution (componentStabilizer first)) := by
  let vertex : CFSG.OrderReductions.TwoPointInvolutions.ComponentVertices first :=
    ⟨involution, (componentStabilizer_involution_iff first involution).mp mem_first⟩
  have stabilizer_eq : MulAction.stabilizer
      (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second) involution =
      MulAction.stabilizer (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second) vertex := by
    ext element
    change element.val • involution = involution ↔ element • vertex = vertex
    constructor
    · intro fixed
      exact Subtype.ext fixed
    · intro fixed
      exact congrArg Subtype.val fixed
  have := CFSG.OrderReductions.TwoPointInvolutions.pair_transitive_on_vertices first second distinct
  rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer, stabilizer_eq,
    MulAction.index_stabilizer_of_transitive]
  exact Nat.card_congr (CFSG.OrderReductions.TwoPointInvolutions.componentVerticesEquiv first)

theorem involution_normalizer_gives_three_fixed {group : Type*} [Group group] [Finite group]
    (first second : Component group) (distinct : first ≠ second)
    (subgroup : Subgroup group) (contains : subgroup ≤ CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second)
    (involution : Involution group) (mem_first : involution.val ∈ componentStabilizer first)
    (normalizes : involution.val ∈ Subgroup.normalizer (subgroup : Set group)) :
    3 ≤ Nat.card (MulAction.fixedPoints subgroup (Component group)) := by
  classical
  have first_fixed : first ∈ MulAction.fixedPoints subgroup (Component group) := by
    apply MulAction.mem_fixedPoints.mpr
    intro element
    exact (contains element.property).1
  have second_fixed : second ∈ MulAction.fixedPoints subgroup (Component group) := by
    apply MulAction.mem_fixedPoints.mpr
    intro element
    exact (contains element.property).2
  have moved_fixed := CFSG.OrderReductions.FixedPairSylow.normalizer_preserves_fixedPoints subgroup
    involution.val normalizes second_fixed
  have fixes_first := MulAction.mem_stabilizer_iff.mp mem_first
  have moved_ne_first : involution.val • second ≠ first := by
    intro equal_image
    exact distinct (MulAction.injective involution.val (fixes_first.trans equal_image.symm))
  have moved_ne_second : involution.val • second ≠ second := by
    intro fixes_second
    exact distinct (CFSG.OrderReductions.MaximalThreePoint.involution_fixed_component_unique
      involution first second fixes_first fixes_second)
  let := Fintype.ofFinite (MulAction.fixedPoints subgroup (Component group))
  let first_vertex : MulAction.fixedPoints subgroup (Component group) := ⟨first, first_fixed⟩
  let second_vertex : MulAction.fixedPoints subgroup (Component group) := ⟨second, second_fixed⟩
  let moved_vertex : MulAction.fixedPoints subgroup (Component group) :=
    ⟨involution.val • second, moved_fixed⟩
  have card_gt : 2 < Fintype.card (MulAction.fixedPoints subgroup (Component group)) := by
    apply Fintype.two_lt_card_iff.mpr
    refine ⟨first_vertex, second_vertex, moved_vertex, ?_, ?_, ?_⟩
    · exact fun equal_vertices => distinct (congrArg Subtype.val equal_vertices)
    · exact fun equal_vertices => moved_ne_first (congrArg Subtype.val equal_vertices).symm
    · exact fun equal_vertices => moved_ne_second (congrArg Subtype.val equal_vertices).symm
  rw [← Nat.card_eq_fintype_card] at card_gt
  omega

theorem pRegular_pair_sylow_three_fixed {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (first second : Component group)
    (distinct : first ≠ second)
    (regular : PRegular prime (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second)
      (componentStabilizer first))
    (sylow : Sylow prime (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second)) :
    3 ≤ Nat.card (MulAction.fixedPoints
      ((sylow : Subgroup (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second)).map
        (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second).subtype) (Component group)) := by
  have odd_pair := distinct_componentStabilizers_odd_intersection first second distinct
  have all_even := (pRegular_iff_every_even_normalizer prime
    (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second) (componentStabilizer first)
      inf_le_left odd_pair).mp regular
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨element, element_order⟩ := exists_prime_orderOf_dvd_card' 2 (all_even sylow).two_dvd
  let involution : Involution group :=
    ⟨element.val, (Subgroup.orderOf_coe element).trans element_order⟩
  apply involution_normalizer_gives_three_fixed first second distinct
    ((sylow : Subgroup (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second)).map
      (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second).subtype)
      ?_ involution element.property.2 element.property.1
  intro original mem_image
  obtain ⟨preimage, _, equal_image⟩ := Subgroup.mem_map.mp mem_image
  exact equal_image ▸ preimage.property

theorem pair_conjugates_involutions {group : Type*} [Group group] [Finite group]
    (first second : Component group) (distinct : first ≠ second)
    (source target : Involution group)
    (source_mem : source.val ∈ componentStabilizer first)
    (target_mem : target.val ∈ componentStabilizer first) :
    ∃ conjugator : CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second,
      conjugator.val • source = target := by
  let source_vertex : CFSG.OrderReductions.TwoPointInvolutions.ComponentVertices first :=
    ⟨source, (componentStabilizer_involution_iff first source).mp source_mem⟩
  let target_vertex : CFSG.OrderReductions.TwoPointInvolutions.ComponentVertices first :=
    ⟨target, (componentStabilizer_involution_iff first target).mp target_mem⟩
  have := CFSG.OrderReductions.TwoPointInvolutions.pair_transitive_on_vertices first second distinct
  obtain ⟨conjugator, conjugates⟩ := MulAction.exists_smul_eq
    (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second) source_vertex target_vertex
  exact ⟨conjugator, congrArg Subtype.val conjugates⟩

theorem pRegular_pair_every_involution_invariant_sylow {group : Type*}
    [Group group] [Finite group] (prime : ℕ) [Fact (Nat.Prime prime)]
    (first second : Component group) (distinct : first ≠ second)
    (regular : PRegular prime (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second)
      (componentStabilizer first))
    (involution : Involution group) (mem_first : involution.val ∈ componentStabilizer first) :
    ∃ sylow : Sylow prime (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second),
      involution.val ∈ Subgroup.normalizer
        ((sylow : Subgroup (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second)).map
          (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second).subtype : Set group) := by
  have odd_pair := distinct_componentStabilizers_odd_intersection first second distinct
  obtain ⟨source, source_mem, source_sylow, normalizes⟩ :=
    (pRegular_iff_invariant_sylow prime (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second)
      (componentStabilizer first) odd_pair).mp regular
  obtain ⟨conjugator, conjugates⟩ := pair_conjugates_involutions first second distinct
    source involution source_mem mem_first
  let sylow : Sylow prime (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second) :=
    conjugator • source_sylow
  have image_eq := CFSG.OrderReductions.FixedPairSylow.sylow_subtype_smul_image prime
    (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second) source_sylow conjugator
  refine ⟨sylow, ?_⟩
  rw [image_eq, ← Subgroup.map_normalizer_eq_of_bijective _ (MulAut.conj conjugator.val).bijective]
  have conjugate_value := congrArg Subtype.val conjugates
  rw [involution_smul_val] at conjugate_value
  rw [← conjugate_value]
  exact Subgroup.mem_map_of_mem (MulAut.conj conjugator.val).toMonoidHom normalizes

theorem pRegular_pair_iff_every_involution {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (first second : Component group)
    (distinct : first ≠ second) :
    PRegular prime (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second)
        (componentStabilizer first) ↔
      ∀ involution : Involution group, involution.val ∈ componentStabilizer first →
        primePart prime (Nat.card (intersection (MulAut.conj involution.val)
          (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second))) =
            primePart prime (Nat.card (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second)) := by
  constructor
  · intro regular involution mem_first
    obtain ⟨sylow, normalizes⟩ := pRegular_pair_every_involution_invariant_sylow
      prime first second distinct regular involution mem_first
    apply (invariant_sylow_intersection_iff prime (MulAut.conj involution.val)
      (involution_conjugation_involutive involution)
        (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second)
        (distinct_componentStabilizers_odd_intersection first second distinct)).mpr
    exact ⟨sylow, Subgroup.mem_normalizer_iff_map_conj_eq.mp normalizes⟩
  · intro all_regular
    induction first using SimpleGraph.ConnectedComponent.ind with
    | h vertex =>
      exact ⟨vertex, involution_mem_componentStabilizer vertex,
        all_regular vertex (involution_mem_componentStabilizer vertex)⟩

theorem invariant_pair_sylow_involution_orbit_card {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (first second : Component group)
    (distinct : first ≠ second)
    (sylow : Sylow prime (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second))
    (involution : Involution group) (mem_first : involution.val ∈ componentStabilizer first)
    (normalizes : involution.val ∈ Subgroup.normalizer
      ((sylow : Subgroup (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second)).map
        (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second).subtype : Set group)) :
    Nat.card (MulAction.orbit
      ((sylow : Subgroup (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second)).map
        (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second).subtype) involution) =
      primePart prime (Nat.card (Involution (componentStabilizer first))) := by
  have card_eq := CFSG.OrderReductions.InvariantOrbitBound.invariant_sylow_index_eq prime
    (MulAut.conj involution.val) (involution_conjugation_involutive involution)
      (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second)
      (distinct_componentStabilizers_odd_intersection first second distinct) sylow
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp normalizes)
  rw [involution_fixedIndex_eq_orbit_card, involution_fixedIndex_eq_orbit_card,
    pair_involution_orbit_card first second distinct involution mem_first] at card_eq
  exact card_eq

end CFSG.OrderReductions.PrimeRegular
