module

public import CFSG.Assembly.OrderReductions.CharacterInvolutionTerminal

public section

namespace CFSG.OrderReductions.CharacterClassProducts

theorem stable_sum_commutes {field group vector : Type*} [Field field] [Group group]
    [AddCommGroup vector] [Module field vector] (representation : Representation field group vector)
    (elements : Finset group)
    (stable : ∀ conjugator element, element ∈ elements →
      conjugator * element * conjugator⁻¹ ∈ elements) (actor : group) :
    (∑ element ∈ elements, representation element) * representation actor =
      representation actor * (∑ element ∈ elements, representation element) := by
  classical
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_bij' (fun element _ => actor⁻¹ * element * actor)
    (fun element _ => actor * element * actor⁻¹)
  · intro element membership
    simpa only [inv_inv] using stable actor⁻¹ element membership
  · intro element membership
    exact stable actor element membership
  · intro element membership
    group
  · intro element membership
    group
  · intro element membership
    rw [← map_mul, ← map_mul]
    congr 1
    group

theorem stable_sum_scalar {field group vector : Type*} [Field field] [IsAlgClosed field]
    [Group group] [AddCommGroup vector] [Module field vector] [FiniteDimensional field vector]
    (representation : Representation field group vector) [representation.IsIrreducible]
    (elements : Finset group)
    (stable : ∀ conjugator element, element ∈ elements →
      conjugator * element * conjugator⁻¹ ∈ elements) :
    ∃ scalar : field, (∑ element ∈ elements, representation element) =
      scalar • (1 : Module.End field vector) := by
  let intertwining : representation.IntertwiningMap representation :=
    { toLinearMap := ∑ element ∈ elements, representation element
      isIntertwining' := stable_sum_commutes representation elements stable }
  obtain ⟨scalar, equal⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := representation)).surjective intertwining
  have linear_equal := congrArg Representation.IntertwiningMap.toLinearMap equal
  rw [Representation.IntertwiningMap.algebraMap_apply] at linear_equal
  exact ⟨scalar, linear_equal.symm⟩

theorem character_pair_sum {field group vector : Type*} [Field field] [IsAlgClosed field]
    [Group group] [AddCommGroup vector] [Module field vector] [FiniteDimensional field vector]
    (representation : Representation field group vector) [representation.IsIrreducible]
    (elements : Finset group)
    (stable : ∀ conjugator element, element ∈ elements →
      conjugator * element * conjugator⁻¹ ∈ elements)
    (value : field) (constant : ∀ element ∈ elements, representation.character element = value)
    (degree_ne_zero : representation.character 1 ≠ 0) :
    (∑ first ∈ elements, ∑ second ∈ elements, representation.character (first * second)) =
      (elements.card : field) ^ 2 * value ^ 2 / representation.character 1 := by
  classical
  obtain ⟨scalar, scalar_eq⟩ := stable_sum_scalar representation elements stable
  have trace_sum : LinearMap.trace field vector (∑ element ∈ elements, representation element) =
      (elements.card : field) * value := by
    rw [map_sum]
    change (∑ element ∈ elements, representation.character element) = _
    rw [Finset.sum_congr rfl constant, Finset.sum_const, nsmul_eq_mul]
  have scalar_degree : scalar * representation.character 1 = (elements.card : field) * value := by
    rw [scalar_eq, map_smul] at trace_sum
    simpa only [Representation.character, map_one, smul_eq_mul] using trace_sum
  have scalar_value : scalar = (elements.card : field) * value / representation.character 1 :=
    (eq_div_iff degree_ne_zero).mpr scalar_degree
  have trace_product :
      (∑ first ∈ elements, ∑ second ∈ elements, representation.character (first * second)) =
        scalar ^ 2 * representation.character 1 := by
    calc
      _ = LinearMap.trace field vector
          ((∑ element ∈ elements, representation element) *
            (∑ element ∈ elements, representation element)) := by
        rw [Finset.sum_mul_sum, map_sum]
        apply Finset.sum_congr rfl
        intro first first_mem
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro second second_mem
        simp only [Representation.character, map_mul]
      _ = scalar ^ 2 * representation.character 1 := by
        rw [scalar_eq, smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, map_smul]
        simp only [pow_two, Representation.character, map_one, smul_eq_mul]
  rw [trace_product, scalar_value]
  field_simp

@[expose] noncomputable def conjugacyFinset {group : Type*} [Group group] [Finite group]
    (element : group) : Finset group := (conjugatesOf element).toFinite.toFinset

theorem mem_conjugacyFinset {group : Type*} [Group group] [Finite group]
    (element candidate : group) : candidate ∈ conjugacyFinset element ↔ IsConj element candidate := by
  exact (conjugatesOf element).toFinite.mem_toFinset

theorem conjugacyFinset_stable {group : Type*} [Group group] [Finite group]
    (element conjugator candidate : group) (membership : candidate ∈ conjugacyFinset element) :
    conjugator * candidate * conjugator⁻¹ ∈ conjugacyFinset element := by
  apply (mem_conjugacyFinset element _).mpr
  obtain ⟨witness, witness_eq⟩ := isConj_iff.mp ((mem_conjugacyFinset element candidate).mp membership)
  apply isConj_iff.mpr
  refine ⟨conjugator * witness, ?_⟩
  rw [← witness_eq]
  group

theorem character_constant_on_conjugacyFinset {field group vector : Type*} [Field field]
    [Group group] [Finite group] [AddCommGroup vector] [Module field vector]
    (representation : Representation field group vector) (element candidate : group)
    (membership : candidate ∈ conjugacyFinset element) :
    representation.character candidate = representation.character element := by
  obtain ⟨witness, witness_eq⟩ := isConj_iff.mp ((mem_conjugacyFinset element candidate).mp membership)
  rw [← witness_eq]
  exact representation.char_conj element witness

theorem character_conjugacy_pair_sum {field group vector : Type*} [Field field] [IsAlgClosed field]
    [Group group] [Finite group] [AddCommGroup vector] [Module field vector]
    [FiniteDimensional field vector] (representation : Representation field group vector)
    [representation.IsIrreducible] (element : group) (degree_ne_zero : representation.character 1 ≠ 0) :
    (∑ first ∈ conjugacyFinset element, ∑ second ∈ conjugacyFinset element,
      representation.character (first * second)) =
      ((conjugacyFinset element).card : field) ^ 2 * representation.character element ^ 2 /
        representation.character 1 :=
  character_pair_sum representation (conjugacyFinset element) (conjugacyFinset_stable element)
    (representation.character element) (character_constant_on_conjugacyFinset representation element)
    degree_ne_zero

theorem norm_three_character_rigidity {field group first_vector second_vector : Type*}
    [Field field] [CharZero field] [IsAlgClosed field] [Group group] [Finite group]
    [AddCommGroup first_vector] [Module field first_vector] [FiniteDimensional field first_vector]
    [AddCommGroup second_vector] [Module field second_vector] [FiniteDimensional field second_vector]
    (first : Representation field group first_vector) [first.IsIrreducible]
    (second : Representation field group second_vector) [second.IsIrreducible]
    (element : group) (first_coefficient second_coefficient : field)
    (first_coefficient_ne_zero : first_coefficient ≠ 0)
    (second_coefficient_ne_zero : second_coefficient ≠ 0)
    (first_degree_ne_zero : first.character 1 ≠ 0) (second_degree_ne_zero : second.character 1 ≠ 0)
    (degree_relation : 1 + first_coefficient * first.character 1 -
      second_coefficient * second.character 1 = 0)
    (value_relation : 1 + first_coefficient * first.character element -
      second_coefficient * second.character element = 0)
    (pair_sum : (∑ left ∈ conjugacyFinset element, ∑ right ∈ conjugacyFinset element,
      (1 + first_coefficient * first.character (left * right) -
        second_coefficient * second.character (left * right))) = 0) :
    first.character element = first.character 1 := by
  classical
  have class_nonempty : (conjugacyFinset element).Nonempty :=
    ⟨element, (mem_conjugacyFinset element element).mpr (IsConj.refl element)⟩
  have class_card_ne_zero : ((conjugacyFinset element).card : field) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt class_nonempty.card_pos)
  have first_sum := character_conjugacy_pair_sum first element first_degree_ne_zero
  have second_sum := character_conjugacy_pair_sum second element second_degree_ne_zero
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul] at pair_sum
  rw [first_sum, second_sum] at pair_sum
  field_simp [first_degree_ne_zero, second_degree_ne_zero] at pair_sum
  simp only [mul_zero] at pair_sum
  have reduced := (mul_eq_zero.mp pair_sum).resolve_left (pow_ne_zero 2 class_card_ne_zero)
  have quadratic : 1 + (first_coefficient * first.character element) ^ 2 /
      (first_coefficient * first.character 1) -
      (second_coefficient * second.character element) ^ 2 /
        (second_coefficient * second.character 1) = 0 := by
    field_simp [first_coefficient_ne_zero, second_coefficient_ne_zero,
      first_degree_ne_zero, second_degree_ne_zero]
    linear_combination reduced
  have signed_equal := CFSG.OrderReductions.CharacterInvolutionTerminal.norm_three_value_eq_degree
    (first_coefficient * first.character 1) (second_coefficient * second.character 1)
    (first_coefficient * first.character element) (second_coefficient * second.character element)
    (mul_ne_zero first_coefficient_ne_zero first_degree_ne_zero)
    (mul_ne_zero second_coefficient_ne_zero second_degree_ne_zero)
    degree_relation value_relation quadratic
  exact mul_left_cancel₀ first_coefficient_ne_zero signed_equal

theorem proper_normal_of_norm_three_class_square {field group first_vector second_vector : Type*}
    [Field field] [CharZero field] [IsAlgClosed field] [Group group] [Finite group]
    [AddCommGroup first_vector] [Module field first_vector] [FiniteDimensional field first_vector]
    [AddCommGroup second_vector] [Module field second_vector] [FiniteDimensional field second_vector]
    (first : Representation field group first_vector) [first.IsIrreducible]
    (second : Representation field group second_vector) [second.IsIrreducible]
    (nontrivial_first : first ≠ 1) (involution : CFSG.OrderReductions.InvolutionGraph.Involution group)
    (first_coefficient second_coefficient : field)
    (first_coefficient_ne_zero : first_coefficient ≠ 0)
    (second_coefficient_ne_zero : second_coefficient ≠ 0)
    (first_degree_ne_zero : first.character 1 ≠ 0) (second_degree_ne_zero : second.character 1 ≠ 0)
    (degree_relation : 1 + first_coefficient * first.character 1 -
      second_coefficient * second.character 1 = 0)
    (value_relation : 1 + first_coefficient * first.character involution.val -
      second_coefficient * second.character involution.val = 0)
    (pair_sum : (∑ left ∈ conjugacyFinset involution.val, ∑ right ∈ conjugacyFinset involution.val,
      (1 + first_coefficient * first.character (left * right) -
        second_coefficient * second.character (left * right))) = 0) :
    ∃ normal : Subgroup group, normal.Normal ∧ normal ≠ ⊤ ∧ involution.val ∈ normal :=
  CFSG.OrderReductions.CharacterInvolutionTerminal.proper_normal_contains_involution_of_character_eq
    first nontrivial_first involution
    (norm_three_character_rigidity first second involution.val first_coefficient second_coefficient
      first_coefficient_ne_zero second_coefficient_ne_zero first_degree_ne_zero second_degree_ne_zero
      degree_relation value_relation pair_sum)

end CFSG.OrderReductions.CharacterClassProducts
