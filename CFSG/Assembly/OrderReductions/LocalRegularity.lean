module

public import CFSG.Assembly.OrderReductions.PrimeRegular

public section

namespace CFSG.OrderReductions.LocalRegularity

open CFSG.OrderReductions.InvolutionGraph
open CFSG.OrderReductions.PrimePart
open CFSG.OrderReductions.TwoPointInvolutions
open CFSG.OrderReductions.PrimeRegular

abbrev InvertedIn {group : Type*} [Group group] (subgroup : Subgroup group)
    (involution : Involution group) :=
  CFSG.OrderReductions.OutsideInvolutions.InvertedBy subgroup involution

theorem inverted_card_mono {group : Type*} [Group group] [Finite group]
    (smaller larger : Subgroup group) (contains : smaller ≤ larger) (involution : Involution group) :
    Nat.card (InvertedIn smaller involution) ≤ Nat.card (InvertedIn larger involution) := by
  let inclusion : InvertedIn smaller involution → InvertedIn larger involution := fun element =>
    ⟨⟨element.val.val, contains element.val.property⟩, element.property⟩
  apply Nat.card_le_card_of_injective inclusion
  intro first second equal_images
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun element : InvertedIn larger involution => element.val.val) equal_images

theorem inverted_card_le_involution_orbit {group : Type*} [Group group] [Finite group]
    (ambient : Subgroup group) (strong : StronglyEmbedded ambient)
    (subgroup : Subgroup group) (contains : subgroup ≤ ambient)
    (inside outside : Involution group) (inside_mem : inside.val ∈ ambient)
    (outside_not_mem : outside.val ∉ ambient) :
    Nat.card (InvertedIn subgroup outside) ≤ Nat.card (MulAction.orbit subgroup inside) := by
  let image : InvertedIn subgroup outside → MulAction.orbit subgroup inside := fun element =>
    ⟨element.val.val • inside, ⟨element.val, rfl⟩⟩
  apply Nat.card_le_card_of_injective image
  intro first second equal_images
  let included : InvertedIn subgroup outside → InvertedIn ambient outside := fun element =>
    ⟨⟨element.val.val, contains element.val.property⟩, element.property⟩
  have equal_conjugates := congrArg Subtype.val equal_images
  have equal_inverted := CFSG.OrderReductions.OutsideInvolutions.inverted_conjugation_injective
    ambient strong inside outside inside_mem outside_not_mem
      (show (included first).val.val • inside = (included second).val.val • inside from equal_conjugates)
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun element : InvertedIn ambient outside => element.val.val) equal_inverted

theorem inverted_card_eq_fixedIndex {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (odd_subgroup : Odd (Nat.card subgroup))
    (involution : Involution group)
    (normalizes : involution.val ∈ Subgroup.normalizer (subgroup : Set group)) :
    Nat.card (InvertedIn subgroup involution) =
      CFSG.OrderReductions.InvariantOrbitBound.fixedIndex (MulAut.conj involution.val) subgroup := by
  have invariant : subgroup.map (MulAut.conj involution.val).toMonoidHom = subgroup :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp normalizes
  let restricted := CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism
    (MulAut.conj involution.val) subgroup invariant
  have inverted_equiv : InvertedIn subgroup involution ≃
      CFSG.OrderReductions.OddInversion.InvertedElements restricted :=
    (Equiv.refl subgroup).subtypeEquiv (fun element => by
      change (MulAut.conj involution.val) element.val = element.val⁻¹ ↔
        restricted element = element⁻¹
      constructor
      · intro inverted
        exact Subtype.ext inverted
      · intro inverted
        exact congrArg Subtype.val inverted)
  have fixed_eq : CFSG.OrderReductions.OddInversion.fixedSubgroup restricted =
      (CFSG.OrderReductions.OddInversion.fixedSubgroup (MulAut.conj involution.val)).subgroupOf subgroup := by
    ext element
    change restricted element = element ↔ (MulAut.conj involution.val) element.val = element.val
    exact Subtype.ext_iff
  rw [Nat.card_congr inverted_equiv,
    CFSG.OrderReductions.OddInversion.inverted_card_eq_fixed_index restricted
      (CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism_involutive
        (MulAut.conj involution.val) (involution_conjugation_involutive involution) subgroup invariant)
      odd_subgroup, fixed_eq]
  rfl

theorem flip_fixedIndex_eq_involution_card {group : Type*} [Group group] [Finite group]
    (first second : Component group) (distinct : first ≠ second) (flip : Involution group)
    (first_moves : flip.val • first = second) (second_moves : flip.val • second = first) :
    CFSG.OrderReductions.InvariantOrbitBound.fixedIndex (MulAut.conj flip.val) (pairSubgroup first second) =
      Nat.card (Involution (componentStabilizer first)) := by
  have fixed_eq : CFSG.OrderReductions.OddInversion.fixedSubgroup
      (flipAutomorphism first second flip first_moves second_moves) =
      (CFSG.OrderReductions.OddInversion.fixedSubgroup (MulAut.conj flip.val)).subgroupOf
        (pairSubgroup first second) := by
    ext element
    change flipAutomorphism first second flip first_moves second_moves element = element ↔
      (MulAut.conj flip.val) element.val = element.val
    constructor
    · intro fixed
      exact congrArg Subtype.val fixed
    · intro fixed
      exact Subtype.ext fixed
  rw [← flip_fixed_index_eq_involution_card first second distinct flip first_moves second_moves,
    fixed_eq]
  rfl

theorem sylow_flip_inverted_card {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (first second : Component group)
    (distinct : first ≠ second) (sylow : Sylow prime (pairSubgroup first second))
    (flip : Involution group)
    (normalizes : flip.val ∈ Subgroup.normalizer
      ((sylow : Subgroup (pairSubgroup first second)).map
        (pairSubgroup first second).subtype : Set group))
    (first_moves : flip.val • first = second) (second_moves : flip.val • second = first) :
    Nat.card (InvertedIn ((sylow : Subgroup (pairSubgroup first second)).map
      (pairSubgroup first second).subtype) flip) =
      primePart prime (Nat.card (Involution (componentStabilizer first))) := by
  have odd_pair := distinct_componentStabilizers_odd_intersection first second distinct
  have odd_image : Odd (Nat.card ((sylow : Subgroup (pairSubgroup first second)).map
      (pairSubgroup first second).subtype)) := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective]
    exact odd_pair.of_dvd_nat sylow.card_subgroup_dvd_card
  rw [inverted_card_eq_fixedIndex _ odd_image flip normalizes,
    CFSG.OrderReductions.InvariantOrbitBound.invariant_sylow_index_eq prime (MulAut.conj flip.val)
      (involution_conjugation_involutive flip) (pairSubgroup first second) odd_pair sylow
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp normalizes),
    flip_fixedIndex_eq_involution_card first second distinct flip first_moves second_moves]

theorem component_involution_card_eq {group : Type*} [Group group] [Finite group]
    (first second : Component group) :
    Nat.card (Involution (componentStabilizer first)) =
      Nat.card (Involution (componentStabilizer second)) := by
  rw [← Nat.card_congr (componentVerticesEquiv first),
    ← Nat.card_congr (componentVerticesEquiv second)]
  exact componentVertices_card_eq first second

theorem maximal_regular_pair_is_sylow {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (subgroup : Subgroup group)
    (maximal : Maximal
      (CFSG.OrderReductions.MaximalThreePoint.ThreePointPrime (points := Component group) prime) subgroup)
    (first second : Component group) (distinct : first ≠ second)
    (first_fixed : first ∈ MulAction.fixedPoints subgroup (Component group))
    (second_fixed : second ∈ MulAction.fixedPoints subgroup (Component group))
    (regular : PRegular prime (pairSubgroup first second) (componentStabilizer first)) :
    ∃ sylow : Sylow prime (pairSubgroup first second),
      (sylow : Subgroup (pairSubgroup first second)).map
        (pairSubgroup first second).subtype = subgroup := by
  have subgroup_le : subgroup ≤ pairSubgroup first second := by
    intro element mem_subgroup
    exact ⟨MulAction.mem_fixedPoints.mp first_fixed ⟨element, mem_subgroup⟩,
      MulAction.mem_fixedPoints.mp second_fixed ⟨element, mem_subgroup⟩⟩
  have internal_prime : IsPGroup prime (subgroup.subgroupOf (pairSubgroup first second)) :=
    maximal.prop.1.of_equiv (Subgroup.subgroupOfEquivOfLe subgroup_le).symm
  obtain ⟨sylow, internal_contains⟩ := internal_prime.exists_le_sylow
  let image := (sylow : Subgroup (pairSubgroup first second)).map
    (pairSubgroup first second).subtype
  have subgroup_contains : subgroup ≤ image := by
    rw [← Subgroup.map_subgroupOf_eq_of_le subgroup_le]
    exact Subgroup.map_mono internal_contains
  have image_three : CFSG.OrderReductions.MaximalThreePoint.ThreePointPrime
      (points := Component group) prime image :=
    ⟨sylow.isPGroup'.map (pairSubgroup first second).subtype,
      pRegular_pair_sylow_three_fixed prime first second distinct regular sylow⟩
  exact ⟨sylow, (maximal.eq_of_le image_three subgroup_contains).symm⟩

theorem maximal_even_point_normalizer_regular {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (subgroup : Subgroup group)
    (maximal : Maximal
      (CFSG.OrderReductions.MaximalThreePoint.ThreePointPrime (points := Component group) prime) subgroup)
    (initial_first initial_second : Component group) (initial_distinct : initial_first ≠ initial_second)
    (initial_sylow : Sylow prime (pairSubgroup initial_first initial_second))
    (initial_contains : (initial_sylow : Subgroup (pairSubgroup initial_first initial_second)).map
      (pairSubgroup initial_first initial_second).subtype ≤ subgroup)
    (first second : Component group) (distinct : first ≠ second)
    (first_fixed : first ∈ MulAction.fixedPoints subgroup (Component group))
    (second_fixed : second ∈ MulAction.fixedPoints subgroup (Component group))
    (even_normalizer : Even (Nat.card ↥(Subgroup.normalizer (subgroup : Set group) ⊓
      componentStabilizer first))) :
    PRegular prime (pairSubgroup first second) (componentStabilizer first) ∧
      ∃ sylow : Sylow prime (pairSubgroup first second),
        (sylow : Subgroup (pairSubgroup first second)).map
          (pairSubgroup first second).subtype = subgroup := by
  obtain ⟨flip, flip_normalizes, initial_moves, initial_reverse⟩ :=
    CFSG.OrderReductions.TwoPointSylow.exists_sylow_normalizing_flip prime initial_first initial_second
      initial_distinct initial_sylow
  let initial_image := (initial_sylow : Subgroup (pairSubgroup initial_first initial_second)).map
    (pairSubgroup initial_first initial_second).subtype
  have initial_count := sylow_flip_inverted_card prime initial_first initial_second initial_distinct
    initial_sylow flip flip_normalizes initial_moves initial_reverse
  have count_equal := component_involution_card_eq initial_first first
  rw [count_equal] at initial_count
  have subgroup_le : subgroup ≤ pairSubgroup first second := by
    intro element mem_subgroup
    exact ⟨MulAction.mem_fixedPoints.mp first_fixed ⟨element, mem_subgroup⟩,
      MulAction.mem_fixedPoints.mp second_fixed ⟨element, mem_subgroup⟩⟩
  have odd_pair := distinct_componentStabilizers_odd_intersection first second distinct
  have regular : PRegular prime (pairSubgroup first second) (componentStabilizer first) := by
    apply (pRegular_iff_prime_orbit_large prime (pairSubgroup first second)
      (componentStabilizer first) odd_pair).mpr
    by_cases flip_inside : flip.val ∈ componentStabilizer first
    · have initial_prime : IsPGroup prime initial_image :=
        initial_sylow.isPGroup'.map (pairSubgroup initial_first initial_second).subtype
      have initial_odd : Odd (Nat.card initial_image) :=
        odd_pair.of_dvd_nat (Subgroup.card_dvd_of_le (initial_contains.trans subgroup_le))
      have orbit_count : Nat.card (MulAction.orbit initial_image flip) =
          primePart prime (Nat.card (Involution (componentStabilizer first))) := by
        rw [← involution_fixedIndex_eq_orbit_card,
          ← inverted_card_eq_fixedIndex initial_image initial_odd flip flip_normalizes]
        exact initial_count
      refine ⟨flip, flip_inside, initial_image, initial_prime,
        initial_contains.trans subgroup_le, flip_normalizes, ?_⟩
      rw [pair_involution_orbit_card first second distinct flip flip_inside, orbit_count]
    · have : Fact (Nat.Prime 2) := ⟨by decide⟩
      obtain ⟨element, element_order⟩ := exists_prime_orderOf_dvd_card' 2 even_normalizer.two_dvd
      let inside : Involution group :=
        ⟨element.val, (Subgroup.orderOf_coe element).trans element_order⟩
      have inside_mem : inside.val ∈ componentStabilizer first := element.property.2
      have strong := componentStabilizer_stronglyEmbedded first ⟨second, distinct.symm⟩
      have lower_bound := inverted_card_mono initial_image subgroup initial_contains flip
      have upper_bound := inverted_card_le_involution_orbit (componentStabilizer first) strong
        subgroup (subgroup_le.trans inf_le_left) inside flip inside_mem flip_inside
      rw [initial_count] at lower_bound
      refine ⟨inside, inside_mem, subgroup, maximal.prop.1, subgroup_le, element.property.1, ?_⟩
      rw [pair_involution_orbit_card first second distinct inside inside_mem]
      exact lower_bound.trans upper_bound
  exact ⟨regular, maximal_regular_pair_is_sylow prime subgroup maximal first second distinct
    first_fixed second_fixed regular⟩

theorem normalizer_point_card_conjugate {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (first second : Component group) (conjugator : group)
    (normalizes : conjugator ∈ Subgroup.normalizer (subgroup : Set group))
    (moves : conjugator • first = second) :
    Nat.card ↥(Subgroup.normalizer (subgroup : Set group) ⊓ componentStabilizer first) =
      Nat.card ↥(Subgroup.normalizer (subgroup : Set group) ⊓ componentStabilizer second) := by
  have invariant : subgroup.map (MulAut.conj conjugator).toMonoidHom = subgroup :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp normalizes
  have mapped : (Subgroup.normalizer (subgroup : Set group) ⊓ componentStabilizer first).map
      (MulAut.conj conjugator).toMonoidHom =
      Subgroup.normalizer (subgroup : Set group) ⊓ componentStabilizer second := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj conjugator).injective,
      Subgroup.map_normalizer_eq_of_bijective _ (MulAut.conj conjugator).bijective,
      invariant, ← componentStabilizer_smul, moves]
  rw [← mapped, Subgroup.card_map_of_injective (MulAut.conj conjugator).injective]

theorem maximal_all_point_normalizers_even {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (subgroup : Subgroup group)
    (maximal : Maximal
      (CFSG.OrderReductions.MaximalThreePoint.ThreePointPrime (points := Component group) prime) subgroup)
    (initial_first initial_second : Component group) (initial_distinct : initial_first ≠ initial_second)
    (initial_sylow : Sylow prime (pairSubgroup initial_first initial_second))
    (initial_contains : (initial_sylow : Subgroup (pairSubgroup initial_first initial_second)).map
      (pairSubgroup initial_first initial_second).subtype ≤ subgroup)
    (base : Component group) (base_fixed : base ∈ MulAction.fixedPoints subgroup (Component group))
    (base_even : Even (Nat.card ↥(Subgroup.normalizer (subgroup : Set group) ⊓
      componentStabilizer base)))
    (point : Component group) (point_fixed : point ∈ MulAction.fixedPoints subgroup (Component group)) :
    Even (Nat.card ↥(Subgroup.normalizer (subgroup : Set group) ⊓ componentStabilizer point)) := by
  by_cases equal_base : base = point
  · rwa [← equal_base]
  · obtain ⟨_, sylow, equal_subgroup⟩ := maximal_even_point_normalizer_regular prime subgroup maximal
      initial_first initial_second initial_distinct initial_sylow initial_contains
      base point equal_base base_fixed point_fixed base_even
    obtain ⟨flip, normalizes, moves, _⟩ :=
      CFSG.OrderReductions.TwoPointSylow.exists_sylow_normalizing_flip prime base point equal_base sylow
    rw [equal_subgroup] at normalizes
    rw [← normalizer_point_card_conjugate subgroup base point flip.val normalizes moves]
    exact base_even

theorem maximal_uniform_regular_of_even_point {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (subgroup : Subgroup group)
    (maximal : Maximal
      (CFSG.OrderReductions.MaximalThreePoint.ThreePointPrime (points := Component group) prime) subgroup)
    (initial_first initial_second : Component group) (initial_distinct : initial_first ≠ initial_second)
    (initial_sylow : Sylow prime (pairSubgroup initial_first initial_second))
    (initial_contains : (initial_sylow : Subgroup (pairSubgroup initial_first initial_second)).map
      (pairSubgroup initial_first initial_second).subtype ≤ subgroup)
    (base : Component group) (base_fixed : base ∈ MulAction.fixedPoints subgroup (Component group))
    (base_even : Even (Nat.card ↥(Subgroup.normalizer (subgroup : Set group) ⊓
      componentStabilizer base)))
    (first second : Component group) (distinct : first ≠ second)
    (first_fixed : first ∈ MulAction.fixedPoints subgroup (Component group))
    (second_fixed : second ∈ MulAction.fixedPoints subgroup (Component group)) :
    PRegular prime (pairSubgroup first second) (componentStabilizer first) ∧
      ∃ sylow : Sylow prime (pairSubgroup first second),
        (sylow : Subgroup (pairSubgroup first second)).map
          (pairSubgroup first second).subtype = subgroup := by
  exact maximal_even_point_normalizer_regular prime subgroup maximal initial_first initial_second
    initial_distinct initial_sylow initial_contains first second distinct first_fixed second_fixed
      (maximal_all_point_normalizers_even prime subgroup maximal initial_first initial_second
        initial_distinct initial_sylow initial_contains base base_fixed base_even first first_fixed)

end CFSG.OrderReductions.LocalRegularity
