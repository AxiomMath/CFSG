module

public import CFSG.Assembly.OrderReductions.FixedNormalizerAction
public import CFSG.Assembly.OrderReductions.MaximalThreePoint

public section

namespace CFSG.OrderReductions.MaximalNormalizerAction

open CFSG.OrderReductions.FixedPairSylow
open CFSG.OrderReductions.FixedNormalizerAction

@[expose] def PointThreePointPrime {group points : Type*} [Group group] [MulAction group points]
    (prime : ℕ) (base : points) (subgroup : Subgroup group) : Prop :=
  CFSG.OrderReductions.MaximalThreePoint.ThreePointPrime (points := points) prime subgroup ∧
    subgroup ≤ MulAction.stabilizer group base

theorem maximal_normalizer_two_transitive {group points : Type*} [Group group] [Finite group]
    [MulAction group points] [Finite points]
    (prime : ℕ) [Fact (Nat.Prime prime)]
    (two_transitive : MulAction.IsMultiplyPretransitive group points 2)
    (base : points) (subgroup : Subgroup group)
    (maximal : Maximal (PointThreePointPrime prime base) subgroup) :
    let _ := fixedPointAction (points := points) subgroup
    MulAction.IsMultiplyPretransitive (Subgroup.normalizer (subgroup : Set group))
      (MulAction.fixedPoints subgroup points) 2 := by
  classical
  let normalizer := Subgroup.normalizer (subgroup : Set group)
  let := fixedPointAction (points := points) subgroup
  let fixed_base : MulAction.fixedPoints subgroup points :=
    ⟨base, MulAction.mem_fixedPoints.mpr fun element => maximal.prop.2 element.property⟩
  have fixed_card : 3 ≤ Nat.card (MulAction.fixedPoints subgroup points) := maximal.prop.1.2
  let := Fintype.ofFinite (MulAction.fixedPoints subgroup points)
  obtain ⟨other, other_distinct⟩ := Fintype.exists_ne_of_one_lt_card
    (by rw [← Nat.card_eq_fintype_card]; omega) fixed_base
  have base_distinct : base ≠ other.val := fun equal => other_distinct (Subtype.ext equal.symm)
  have contained_at_pair (first second : MulAction.fixedPoints subgroup points) :
      subgroup ≤ MulAction.stabilizer group first.val ⊓ MulAction.stabilizer group second.val := by
    intro element element_mem
    exact ⟨MulAction.mem_fixedPoints.mp first.property ⟨element, element_mem⟩,
      MulAction.mem_fixedPoints.mp second.property ⟨element, element_mem⟩⟩
  by_cases is_sylow : ∃ sylow : Sylow prime
      ↥(MulAction.stabilizer group base ⊓ MulAction.stabilizer group other.val),
    (sylow : Subgroup ↥(MulAction.stabilizer group base ⊓ MulAction.stabilizer group other.val)).map
      (MulAction.stabilizer group base ⊓ MulAction.stabilizer group other.val).subtype = subgroup
  · obtain ⟨sylow, image_eq⟩ := is_sylow
    have result := sylow_pair_normalizer_two_transitive prime two_transitive base other.val base_distinct sylow
    rw [image_eq] at result
    exact result
  · have not_sylow_at_pair (first second : MulAction.fixedPoints subgroup points) (distinct : first ≠ second) :
        ¬ ∃ sylow : Sylow prime
          ↥(MulAction.stabilizer group first.val ⊓ MulAction.stabilizer group second.val),
          (sylow : Subgroup ↥(MulAction.stabilizer group first.val ⊓ MulAction.stabilizer group second.val)).map
            (MulAction.stabilizer group first.val ⊓ MulAction.stabilizer group second.val).subtype = subgroup := by
      rintro ⟨sylow, image_eq⟩
      apply is_sylow
      apply CFSG.OrderReductions.PrimePart.exists_sylow_image_of_card
      · exact contained_at_pair fixed_base other
      · have card_eq := CFSG.OrderReductions.PrimePart.sylow_map_card_eq_primePart prime _ sylow
        have same_card := congrArg (fun candidate : Subgroup group => Nat.card candidate) image_eq
        exact same_card.symm.trans (card_eq.trans (congrArg (CFSG.OrderReductions.PrimePart.primePart prime)
          (pair_stabilizer_card_eq two_transitive first.val second.val base other.val
            (fun equal => distinct (Subtype.ext equal)) base_distinct)))
    have larger_at_pair (first second : MulAction.fixedPoints subgroup points) (distinct : first ≠ second) :
        ∃ larger : Subgroup group, IsPGroup prime larger ∧ subgroup < larger ∧
          larger ≤ normalizer ⊓ (MulAction.stabilizer group first.val ⊓ MulAction.stabilizer group second.val) :=
      exists_larger_prime_subgroup_in_normalizer_within prime subgroup _ (contained_at_pair first second)
        maximal.prop.1.1 (not_sylow_at_pair first second distinct)
    have realizes (second : MulAction.fixedPoints subgroup points) (distinct : fixed_base ≠ second) :
        ∃ internal : Subgroup normalizer, IsPGroup prime internal ∧
          MulAction.fixedPoints internal (MulAction.fixedPoints subgroup points) = {fixed_base, second} := by
      obtain ⟨larger, larger_prime, strictly_larger, larger_le⟩ := larger_at_pair fixed_base second distinct
      have full_pair : MulAction.fixedPoints larger points = {base, second.val} := by
        apply CFSG.OrderReductions.MaximalThreePoint.fixedPoints_le_two_eq_pair larger base second.val
          (fun equal => distinct (Subtype.ext equal))
          (MulAction.mem_fixedPoints.mpr fun element => (larger_le element.property).2.1)
          (MulAction.mem_fixedPoints.mpr fun element => (larger_le element.property).2.2)
        by_contra large
        have larger_prop : PointThreePointPrime prime base larger :=
          ⟨⟨larger_prime, by omega⟩, larger_le.trans (inf_le_right.trans inf_le_left)⟩
        exact strictly_larger.ne (maximal.eq_of_le larger_prop strictly_larger.le)
      let internal := larger.subgroupOf normalizer
      have contains : larger ≤ normalizer := larger_le.trans inf_le_left
      refine ⟨internal, larger_prime.of_equiv (Subgroup.subgroupOfEquivOfLe contains).symm, ?_⟩
      ext fixed
      have fixed_iff : fixed ∈ MulAction.fixedPoints internal (MulAction.fixedPoints subgroup points) ↔
          fixed.val ∈ MulAction.fixedPoints larger points :=
        mem_restricted_fixedPoints_iff subgroup larger contains fixed
      rw [fixed_iff, full_pair]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro alternatives
        exact alternatives.elim (fun equal => Or.inl (Subtype.ext equal))
          (fun equal => Or.inr (Subtype.ext equal))
      · intro alternatives
        exact alternatives.elim (fun equal => Or.inl (congrArg Subtype.val equal))
          (fun equal => Or.inr (congrArg Subtype.val equal))
    have two_others : ∃ first second : MulAction.fixedPoints subgroup points,
        first ≠ fixed_base ∧ second ≠ fixed_base ∧ first ≠ second := by
      obtain ⟨first, second, third, first_second, first_third, second_third⟩ :=
        Fintype.two_lt_card_iff.mp (by rw [← Nat.card_eq_fintype_card]; omega :
          2 < Fintype.card (MulAction.fixedPoints subgroup points))
      by_cases first_base : first = fixed_base
      · exact ⟨second, third, first_base ▸ first_second.symm, first_base ▸ first_third.symm, second_third⟩
      · by_cases second_base : second = fixed_base
        · exact ⟨first, third, first_base, second_base ▸ second_third.symm, first_third⟩
        · exact ⟨first, second, first_base, second_base, first_second⟩
    have moves : ∃ acting : normalizer, acting • fixed_base ≠ fixed_base := by
      obtain ⟨first, second, first_not_base, second_not_base, distinct⟩ := two_others
      obtain ⟨larger, larger_prime, strictly_larger, larger_le⟩ := larger_at_pair first second distinct
      have not_contained : ¬ larger ≤ MulAction.stabilizer group base := by
        intro contained
        have fixed_large : 3 ≤ Nat.card (MulAction.fixedPoints larger points) := by
          by_contra small
          have pair_eq := CFSG.OrderReductions.MaximalThreePoint.fixedPoints_le_two_eq_pair larger first.val second.val
            (fun equal => distinct (Subtype.ext equal))
            (MulAction.mem_fixedPoints.mpr fun element => (larger_le element.property).2.1)
            (MulAction.mem_fixedPoints.mpr fun element => (larger_le element.property).2.2) (by omega)
          have base_fixed : base ∈ MulAction.fixedPoints larger points :=
            MulAction.mem_fixedPoints.mpr fun element => contained element.property
          rw [pair_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at base_fixed
          rcases base_fixed with equal | equal
          · exact first_not_base (Subtype.ext equal.symm)
          · exact second_not_base (Subtype.ext equal.symm)
        exact strictly_larger.ne (maximal.eq_of_le ⟨⟨larger_prime, fixed_large⟩, contained⟩ strictly_larger.le)
      have outside_exists : ∃ element : group, element ∈ larger ∧ element ∉ MulAction.stabilizer group base := by
        by_contra missing
        apply not_contained
        intro element element_mem
        by_contra not_fixed
        exact missing ⟨element, element_mem, not_fixed⟩
      obtain ⟨element, element_mem, not_fixed⟩ := outside_exists
      exact ⟨⟨element, (larger_le element_mem).1⟩, fun equal => not_fixed (congrArg Subtype.val equal)⟩
    exact pair_realization_two_pretransitive prime fixed_base realizes moves

theorem maximal_global_of_two_transitive {group points : Type*} [Group group] [Finite group]
    [MulAction group points] [Finite points]
    (prime : ℕ) [Fact (Nat.Prime prime)]
    (two_transitive : MulAction.IsMultiplyPretransitive group points 2)
    (base : points) (subgroup : Subgroup group)
    (maximal : Maximal (PointThreePointPrime prime base) subgroup) :
    Maximal (CFSG.OrderReductions.MaximalThreePoint.ThreePointPrime (points := points) prime) subgroup := by
  classical
  let normalizer := Subgroup.normalizer (subgroup : Set group)
  let := fixedPointAction (points := points) subgroup
  have : MulAction.IsMultiplyPretransitive normalizer (MulAction.fixedPoints subgroup points) 2 :=
    maximal_normalizer_two_transitive prime two_transitive base subgroup maximal
  have one_transitive : MulAction.IsMultiplyPretransitive normalizer (MulAction.fixedPoints subgroup points) 1 :=
    MulAction.isMultiplyPretransitive_of_le (by decide : 1 ≤ 2) (by have := maximal.prop.1.2; omega)
  have : MulAction.IsPretransitive normalizer (MulAction.fixedPoints subgroup points) :=
    MulAction.is_one_pretransitive_iff.mp one_transitive
  refine ⟨maximal.prop.1, ?_⟩
  intro larger larger_prop contains
  have larger_nonempty : Nonempty (MulAction.fixedPoints larger points) :=
    (Nat.card_pos_iff.mp (lt_of_lt_of_le (by decide : 0 < 3) larger_prop.2)).1
  obtain ⟨fixed⟩ := larger_nonempty
  let source : MulAction.fixedPoints subgroup points := ⟨fixed.val, fixedPoints_antitone contains fixed.property⟩
  let target : MulAction.fixedPoints subgroup points :=
    ⟨base, MulAction.mem_fixedPoints.mpr fun element => maximal.prop.2 element.property⟩
  obtain ⟨acting, moves⟩ := MulAction.exists_smul_eq normalizer source target
  have moved_fixed : acting.val • fixed.val = base := congrArg Subtype.val moves
  let conjugate := larger.map (MulAut.conj acting.val).toMonoidHom
  have conjugate_prime : IsPGroup prime conjugate := larger_prop.1.map _
  have conjugate_three : 3 ≤ Nat.card (MulAction.fixedPoints conjugate points) := by
    let equivalence : MulAction.fixedPoints larger points ≃ MulAction.fixedPoints conjugate points :=
      { toFun := fun original => ⟨acting.val • original.val,
          conjugate_smul_mem_fixedPoints larger acting.val original.property⟩
        invFun := fun original => ⟨acting.val⁻¹ • original.val, by
          have transported := conjugate_smul_mem_fixedPoints conjugate acting.val⁻¹ original.property
          have composite : (MulAut.conj acting.val⁻¹).toMonoidHom.comp
              (MulAut.conj acting.val).toMonoidHom = MonoidHom.id group := by
            ext element
            change acting.val⁻¹ * (acting.val * element * acting.val⁻¹) * (acting.val⁻¹)⁻¹ = element
            group
          have inverse_image : conjugate.map (MulAut.conj acting.val⁻¹).toMonoidHom = larger := by
            change (larger.map (MulAut.conj acting.val).toMonoidHom).map _ = _
            rw [Subgroup.map_map, composite, Subgroup.map_id]
          exact inverse_image ▸ transported⟩
        left_inv := fun original => Subtype.ext (inv_smul_smul acting.val original.val)
        right_inv := fun original => Subtype.ext (smul_inv_smul acting.val original.val) }
    rw [← Nat.card_congr equivalence]
    exact larger_prop.2
  have conjugate_base : conjugate ≤ MulAction.stabilizer group base := by
    have image_le := Subgroup.map_mono (f := (MulAut.conj acting.val).toMonoidHom)
      (show larger ≤ MulAction.stabilizer group fixed.val from fun element element_mem =>
        MulAction.mem_fixedPoints.mp fixed.property ⟨element, element_mem⟩)
    rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj, moved_fixed] at image_le
    exact image_le
  have subgroup_invariant : subgroup.map (MulAut.conj acting.val).toMonoidHom = subgroup :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp acting.property
  have conjugate_contains : subgroup ≤ conjugate := by
    rw [← subgroup_invariant]
    exact Subgroup.map_mono contains
  have equal_conjugate := maximal.eq_of_le ⟨⟨conjugate_prime, conjugate_three⟩, conjugate_base⟩ conjugate_contains
  have cardinality : Nat.card larger = Nat.card subgroup := by
    have equal_card := congrArg (fun candidate : Subgroup group => Nat.card candidate) equal_conjugate
    change Nat.card subgroup = Nat.card (larger.map (MulAut.conj acting.val).toMonoidHom) at equal_card
    rw [Subgroup.card_map_of_injective (MulAut.conj acting.val).injective] at equal_card
    exact equal_card.symm
  exact (Subgroup.eq_of_le_of_card_ge contains cardinality.le).ge

end CFSG.OrderReductions.MaximalNormalizerAction
