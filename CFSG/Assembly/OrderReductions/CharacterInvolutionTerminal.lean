module

public import CFSG.Assembly.OrderReductions.InvolutionGraph
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.OrderReductions.CharacterInvolutionTerminal

theorem three_term_quadratic_ratio {field : Type*} [Field field]
    (first_degree second_degree third_degree first_value second_value third_value : field)
    (first_ne_zero : first_degree ≠ 0) (second_ne_zero : second_degree ≠ 0)
    (third_ne_zero : third_degree ≠ 0)
    (degree_relation : third_degree = -first_degree - second_degree)
    (value_relation : third_value = first_value + second_value)
    (quadratic : first_value ^ 2 / first_degree + second_value ^ 2 / second_degree +
      third_value ^ 2 / third_degree = 0) :
    first_value / first_degree = second_value / second_degree := by
  have cleared : first_value ^ 2 * second_degree * third_degree +
      second_value ^ 2 * first_degree * third_degree +
      third_value ^ 2 * first_degree * second_degree = 0 := by
    field_simp [first_ne_zero, second_ne_zero, third_ne_zero] at quadratic
    linear_combination quadratic
  have square_zero : (first_value * second_degree - second_value * first_degree) ^ 2 = 0 := by
    rw [degree_relation, value_relation] at cleared
    linear_combination -cleared
  have cross_equal : first_value * second_degree = second_value * first_degree :=
    sub_eq_zero.mp (sq_eq_zero_iff.mp square_zero)
  exact (div_eq_div_iff first_ne_zero second_ne_zero).mpr cross_equal

theorem norm_three_value_eq_degree {field : Type*} [Field field]
    (degree other_degree value other_value : field)
    (degree_ne_zero : degree ≠ 0) (other_degree_ne_zero : other_degree ≠ 0)
    (degree_relation : 1 + degree - other_degree = 0)
    (value_relation : 1 + value - other_value = 0)
    (quadratic : 1 + value ^ 2 / degree - other_value ^ 2 / other_degree = 0) :
    value = degree := by
  have ratio := three_term_quadratic_ratio 1 degree (-other_degree) 1 value other_value
    one_ne_zero degree_ne_zero (neg_ne_zero.mpr other_degree_ne_zero)
    (by linear_combination degree_relation) (by linear_combination -value_relation)
    (by simpa only [one_pow, div_one, div_neg, sub_eq_add_neg] using quadratic)
  have quotient_one : value / degree = 1 := by simpa using ratio.symm
  exact (div_eq_one_iff_eq degree_ne_zero).mp quotient_one

theorem involutive_eq_one_of_trace_eq {field vector : Type*} [Field field] [CharZero field]
    [AddCommGroup vector] [Module field vector] [FiniteDimensional field vector]
    (operator : Module.End field vector) (square_identity : operator * operator = 1)
    (trace_identity : LinearMap.trace field vector operator = LinearMap.trace field vector 1) :
    operator = 1 := by
  have two_ne_zero : (2 : field) ≠ 0 := by norm_num
  have difference_square : (1 - operator) * (1 - operator) = (2 : field) • (1 - operator) := by
    calc
      (1 - operator) * (1 - operator) = 1 - operator - operator + operator * operator := by
        noncomm_ring
      _ = (2 : field) • (1 - operator) := by
        rw [square_identity]
        simp only [two_smul]
        noncomm_ring
  let projection : Module.End field vector := (2 : field)⁻¹ • (1 - operator)
  have idempotent : IsIdempotentElem projection := by
    change ((2 : field)⁻¹ • (1 - operator)) * ((2 : field)⁻¹ • (1 - operator)) =
      (2 : field)⁻¹ • (1 - operator)
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, difference_square, smul_smul]
    congr 1
    field_simp
  have trace_zero : LinearMap.trace field vector projection = 0 := by
    simp only [projection, map_smul, map_sub, trace_identity, sub_self, smul_zero]
  have projection_zero : projection = 0 :=
    LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero idempotent trace_zero
  have difference_zero : (1 : Module.End field vector) - operator = 0 :=
    (smul_eq_zero.mp projection_zero).resolve_left (inv_ne_zero two_ne_zero)
  exact (sub_eq_zero.mp difference_zero).symm

theorem representation_involution_eq_one_of_character_eq {field group vector : Type*}
    [Field field] [CharZero field] [Group group] [AddCommGroup vector] [Module field vector]
    [FiniteDimensional field vector] (representation : Representation field group vector)
    (involution : CFSG.OrderReductions.InvolutionGraph.Involution group)
    (character_identity : representation.character involution.val = representation.character 1) :
    representation involution.val = 1 := by
  apply involutive_eq_one_of_trace_eq
  · have square_identity : involution.val ^ 2 = 1 := by
      simpa only [involution.property] using pow_orderOf_eq_one involution.val
    rw [← pow_two, ← map_pow, square_identity, map_one]
  · simpa only [Representation.character, map_one] using character_identity

theorem proper_normal_contains_involution_of_character_eq {field group vector : Type*}
    [Field field] [CharZero field] [Group group] [AddCommGroup vector] [Module field vector]
    [FiniteDimensional field vector] (representation : Representation field group vector)
    (nontrivial_representation : representation ≠ 1)
    (involution : CFSG.OrderReductions.InvolutionGraph.Involution group)
    (character_identity : representation.character involution.val = representation.character 1) :
    ∃ normal : Subgroup group, normal.Normal ∧ normal ≠ ⊤ ∧ involution.val ∈ normal := by
  refine ⟨representation.asGroupHom.ker, inferInstance, ?_, ?_⟩
  · intro kernel_top
    have trivial_hom := MonoidHom.ker_eq_top_iff.mp kernel_top
    apply nontrivial_representation
    ext element vector_element
    have values_equal := congrArg (fun homomorphism : group →* (Module.End field vector)ˣ =>
      ((homomorphism element : (Module.End field vector)ˣ) : Module.End field vector)) trivial_hom
    exact congrArg (fun current : Module.End field vector => current vector_element) values_equal
  · apply MonoidHom.mem_ker.mpr
    apply Units.ext
    exact representation_involution_eq_one_of_character_eq representation involution character_identity

theorem quaternion_value_eq_degree {field : Type*} [Field field]
    (first_degree second_degree third_degree fourth_degree fifth_degree : field)
    (first_value second_value third_value fourth_value fifth_value : field)
    (first_ne_zero : first_degree ≠ 0) (second_ne_zero : second_degree ≠ 0)
    (third_ne_zero : third_degree ≠ 0) (fourth_ne_zero : fourth_degree ≠ 0)
    (fifth_ne_zero : fifth_degree ≠ 0)
    (degree_fourth : fourth_degree = -second_degree - third_degree)
    (degree_fifth : fifth_degree = -first_degree - third_degree)
    (value_fourth : fourth_value = second_value + third_value)
    (value_fifth : fifth_value = first_value + third_value)
    (quadratic_fourth : second_value ^ 2 / second_degree + third_value ^ 2 / third_degree +
      fourth_value ^ 2 / fourth_degree = 0)
    (quadratic_fifth : first_value ^ 2 / first_degree + third_value ^ 2 / third_degree +
      fifth_value ^ 2 / fifth_degree = 0)
    (degree_relation : 1 + first_degree + second_degree + third_degree = 0)
    (value_relation : 1 + first_value + second_value + third_value = 0) :
    first_value = first_degree := by
  have first_ratio := three_term_quadratic_ratio first_degree third_degree fifth_degree
    first_value third_value fifth_value first_ne_zero third_ne_zero fifth_ne_zero
    degree_fifth value_fifth quadratic_fifth
  have second_ratio := three_term_quadratic_ratio second_degree third_degree fourth_degree
    second_value third_value fourth_value second_ne_zero third_ne_zero fourth_ne_zero
    degree_fourth value_fourth quadratic_fourth
  let ratio := third_value / third_degree
  have first_eq : first_value = ratio * first_degree := (div_eq_iff first_ne_zero).mp first_ratio
  have second_eq : second_value = ratio * second_degree := (div_eq_iff second_ne_zero).mp second_ratio
  have third_eq : third_value = ratio * third_degree := by
    dsimp [ratio]
    rw [div_mul_cancel₀ _ third_ne_zero]
  rw [first_eq, second_eq, third_eq] at value_relation
  have ratio_one : ratio = 1 := by
    linear_combination ratio * degree_relation - value_relation
  simpa only [ratio_one, one_mul] using first_eq

theorem proper_normal_of_norm_three_character_data {field group vector : Type*}
    [Field field] [CharZero field] [Group group] [AddCommGroup vector] [Module field vector]
    [FiniteDimensional field vector] (representation : Representation field group vector)
    (nontrivial_representation : representation ≠ 1)
    (involution : CFSG.OrderReductions.InvolutionGraph.Involution group)
    (coefficient other_degree other_value : field) (coefficient_ne_zero : coefficient ≠ 0)
    (degree_ne_zero : coefficient * representation.character 1 ≠ 0)
    (other_degree_ne_zero : other_degree ≠ 0)
    (degree_relation : 1 + coefficient * representation.character 1 - other_degree = 0)
    (value_relation : 1 + coefficient * representation.character involution.val - other_value = 0)
    (quadratic : 1 + (coefficient * representation.character involution.val) ^ 2 /
      (coefficient * representation.character 1) - other_value ^ 2 / other_degree = 0) :
    ∃ normal : Subgroup group, normal.Normal ∧ normal ≠ ⊤ ∧ involution.val ∈ normal := by
  have values_equal := norm_three_value_eq_degree (coefficient * representation.character 1)
    other_degree (coefficient * representation.character involution.val) other_value
    degree_ne_zero other_degree_ne_zero degree_relation value_relation quadratic
  exact proper_normal_contains_involution_of_character_eq representation nontrivial_representation
    involution (mul_left_cancel₀ coefficient_ne_zero values_equal)

end CFSG.OrderReductions.CharacterInvolutionTerminal
