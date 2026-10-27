module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.OrderReductions.QuadraticDimension

theorem anticommutator_commutes_left {ring : Type*} [Ring ring]
    (first second : ring) (first_square : first * first = 0) :
    Commute (first * second + second * first) first := by
  unfold Commute SemiconjBy
  rw [add_mul, mul_add, mul_assoc second first first, first_square, mul_zero, add_zero,
    ← mul_assoc first first second, first_square, zero_mul, zero_add, mul_assoc]

theorem anticommutator_commutes_right {ring : Type*} [Ring ring]
    (first second : ring) (second_square : second * second = 0) :
    Commute (first * second + second * first) second := by
  simpa only [add_comm] using anticommutator_commutes_left second first second_square

theorem representation_inverse_square_zero {field vector actors : Type*} [Field field]
    [AddCommGroup vector] [Module field vector] [Group actors]
    (representation : Representation field actors vector) (actor : actors)
    (square_zero : (representation actor - 1) * (representation actor - 1) = 0) :
    representation actor⁻¹ = 1 - (representation actor - 1) := by
  have product : representation actor * (1 - (representation actor - 1)) = 1 := by
    calc
      representation actor * (1 - (representation actor - 1)) =
          1 - (representation actor - 1) * (representation actor - 1) := by noncomm_ring
      _ = 1 := by rw [square_zero, sub_zero]
  calc
    representation actor⁻¹ = representation actor⁻¹ * 1 := (mul_one _).symm
    _ = representation actor⁻¹ * (representation actor * (1 - (representation actor - 1))) := by rw [product]
    _ = (representation actor⁻¹ * representation actor) * (1 - (representation actor - 1)) :=
      (mul_assoc _ _ _).symm
    _ = 1 - (representation actor - 1) := by
      rw [← map_mul, inv_mul_cancel, map_one, one_mul]

theorem anticommutator_commutes_representation {field vector actors : Type*} [Field field]
    [AddCommGroup vector] [Module field vector] [Group actors]
    (representation : Representation field actors vector) (first second : actors)
    (generates : Subgroup.closure ({first, second} : Set actors) = ⊤)
    (first_square : (representation first - 1) * (representation first - 1) = 0)
    (second_square : (representation second - 1) * (representation second - 1) = 0)
    (actor : actors) :
    Commute ((representation first - 1) * (representation second - 1) +
      (representation second - 1) * (representation first - 1)) (representation actor) := by
  let parameter := (representation first - 1) * (representation second - 1) +
    (representation second - 1) * (representation first - 1)
  have first_commutes : Commute parameter (representation first) := by
    have commutes := anticommutator_commutes_left (representation first - 1) (representation second - 1) first_square
    have shifted := commutes.add_right (Commute.one_right parameter)
    simpa only [sub_add_cancel] using shifted
  have second_commutes : Commute parameter (representation second) := by
    have commutes := anticommutator_commutes_right (representation first - 1) (representation second - 1) second_square
    have shifted := commutes.add_right (Commute.one_right parameter)
    simpa only [sub_add_cancel] using shifted
  have membership : actor ∈ Subgroup.closure ({first, second} : Set actors) := generates ▸ Subgroup.mem_top actor
  apply Subgroup.closure_induction (p := fun member _ => Commute parameter (representation member))
    ?_ ?_ ?_ ?_ membership
  · intro member member_mem
    rcases member_mem with (rfl | rfl)
    · exact first_commutes
    · exact second_commutes
  · rw [map_one]
    exact Commute.one_right parameter
  · intro left right _ _ left_commutes right_commutes
    rw [map_mul]
    exact left_commutes.mul_right right_commutes
  · intro member _ commutes
    have unit_commutes : Commute parameter (representation.asGroupHom member : Module.End field vector) := commutes
    have inverse_commutes := unit_commutes.units_inv_right
    rw [← map_inv] at inverse_commutes
    exact inverse_commutes

theorem anticommutator_scalar_of_irreducible {field vector actors : Type*} [Field field]
    [IsAlgClosed field] [AddCommGroup vector] [Module field vector] [FiniteDimensional field vector]
    [Group actors] (representation : Representation field actors vector) [representation.IsIrreducible]
    (first second : actors) (generates : Subgroup.closure ({first, second} : Set actors) = ⊤)
    (first_square : (representation first - 1) * (representation first - 1) = 0)
    (second_square : (representation second - 1) * (representation second - 1) = 0) :
    ∃ scalar : field, (representation first - 1) * (representation second - 1) +
      (representation second - 1) * (representation first - 1) = scalar • (1 : Module.End field vector) := by
  let parameter := (representation first - 1) * (representation second - 1) +
    (representation second - 1) * (representation first - 1)
  let intertwining : representation.IntertwiningMap representation :=
    { toLinearMap := parameter
      isIntertwining' := fun actor =>
        (anticommutator_commutes_representation representation first second generates first_square second_square actor).eq }
  obtain ⟨scalar, equal⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := representation)).surjective intertwining
  refine ⟨scalar, ?_⟩
  have linear_equal := congrArg Representation.IntertwiningMap.toLinearMap equal
  rw [Representation.IntertwiningMap.algebraMap_apply] at linear_equal
  exact linear_equal.symm

theorem finrank_le_two_of_scalar_anticommutator {field vector actors : Type*} [Field field]
    [AddCommGroup vector] [Module field vector] [Group actors]
    (representation : Representation field actors vector) [representation.IsIrreducible]
    (first second : actors) (generates : Subgroup.closure ({first, second} : Set actors) = ⊤)
    (first_square : (representation first - 1) * (representation first - 1) = 0)
    (second_square : (representation second - 1) * (representation second - 1) = 0)
    (scalar : field)
    (parameter_eq : (representation first - 1) * (representation second - 1) +
      (representation second - 1) * (representation first - 1) = scalar • (1 : Module.End field vector))
    (first_nonzero : representation first - 1 ≠ 0) : Module.finrank field vector ≤ 2 := by
  classical
  let first_difference := representation first - 1
  let second_difference := representation second - 1
  have exists_nonzero : ∃ original : vector, first_difference original ≠ 0 := by
    by_contra none
    push Not at none
    apply first_nonzero
    exact LinearMap.ext none
  obtain ⟨original, original_nonzero⟩ := exists_nonzero
  let witness := first_difference original
  have first_witness : first_difference witness = 0 :=
    congrArg (fun linear : Module.End field vector => linear original) first_square
  have second_square_apply : ∀ member : vector, second_difference (second_difference member) = 0 :=
    fun member => congrArg (fun linear : Module.End field vector => linear member) second_square
  have cross_witness : first_difference (second_difference witness) = scalar • witness := by
    have equal := congrArg (fun linear : Module.End field vector => linear witness) parameter_eq
    change first_difference (second_difference witness) + second_difference (first_difference witness) = scalar • witness at equal
    rwa [first_witness, map_zero, add_zero] at equal
  let span := Submodule.span field ({witness, second_difference witness} : Set vector)
  have first_preserves : ∀ member ∈ span, first_difference member ∈ span := by
    intro member membership
    obtain ⟨left, right, rfl⟩ := Submodule.mem_span_pair.mp membership
    rw [map_add, map_smul, map_smul, first_witness, cross_witness, smul_zero, zero_add]
    exact span.smul_mem right (span.smul_mem scalar (Submodule.subset_span (by simp)))
  have second_preserves : ∀ member ∈ span, second_difference member ∈ span := by
    intro member membership
    obtain ⟨left, right, rfl⟩ := Submodule.mem_span_pair.mp membership
    rw [map_add, map_smul, map_smul, second_square_apply, smul_zero, add_zero]
    exact span.smul_mem left (Submodule.subset_span (by simp))
  have generator_preserves : ∀ actor ∈ ({first, second} : Set actors), ∀ member ∈ span,
      representation actor member ∈ span := by
    intro actor actor_mem member member_mem
    have equal : representation actor member = (representation actor - 1) member + member := by simp
    rw [equal]
    rcases actor_mem with (rfl | rfl)
    · exact span.add_mem (first_preserves member member_mem) member_mem
    · exact span.add_mem (second_preserves member member_mem) member_mem
  have inverse_preserves : ∀ actor ∈ ({first, second} : Set actors), ∀ member ∈ span,
      representation actor⁻¹ member ∈ span := by
    intro actor actor_mem member member_mem
    rcases actor_mem with (equal | equal)
    · have actor_eq : actor = first := equal
      rw [actor_eq, representation_inverse_square_zero representation first first_square]
      change member - first_difference member ∈ span
      exact span.sub_mem member_mem (first_preserves member member_mem)
    · have actor_eq : actor = second := equal
      rw [actor_eq, representation_inverse_square_zero representation second second_square]
      change member - second_difference member ∈ span
      exact span.sub_mem member_mem (second_preserves member member_mem)
  have invariant : ∀ actor : actors, ∀ member ∈ span, representation actor member ∈ span := by
    intro actor
    have membership : actor ∈ Subgroup.closure ({first, second} : Set actors) := generates ▸ Subgroup.mem_top actor
    apply Subgroup.closure_induction''
      (p := fun acting _ => ∀ member ∈ span, representation acting member ∈ span)
      generator_preserves inverse_preserves ?_ ?_ membership
    · intro member member_mem
      rw [map_one]
      exact member_mem
    · intro left right _ _ left_preserves right_preserves member member_mem
      rw [map_mul]
      exact left_preserves _ (right_preserves member member_mem)
  let subrepresentation : Subrepresentation representation :=
    { toSubmodule := span
      apply_mem_toSubmodule := invariant }
  have span_top : span = ⊤ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top subrepresentation with equal | equal
    · have span_bot : span = ⊥ := congrArg Subrepresentation.toSubmodule equal
      have witness_mem : witness ∈ span := Submodule.subset_span (by simp)
      rw [span_bot] at witness_mem
      exact False.elim (original_nonzero ((Submodule.mem_bot _).mp witness_mem))
    · exact congrArg Subrepresentation.toSubmodule equal
  have bound := finrank_span_le_card (R := field) ({witness, second_difference witness} : Set vector)
  change Module.finrank field span ≤ _ at bound
  rw [span_top, finrank_top] at bound
  apply bound.trans
  rw [Set.toFinset_insert, Set.toFinset_singleton]
  exact (Finset.card_insert_le _ _).trans (by simp)

theorem finrank_le_two_of_quadratic_irreducible {field vector actors : Type*} [Field field]
    [IsAlgClosed field] [AddCommGroup vector] [Module field vector] [FiniteDimensional field vector]
    [Group actors] (representation : Representation field actors vector) [representation.IsIrreducible]
    (first second : actors) (generates : Subgroup.closure ({first, second} : Set actors) = ⊤)
    (first_square : (representation first - 1) * (representation first - 1) = 0)
    (second_square : (representation second - 1) * (representation second - 1) = 0)
    (first_nonzero : representation first - 1 ≠ 0) : Module.finrank field vector ≤ 2 := by
  obtain ⟨scalar, scalar_eq⟩ := anticommutator_scalar_of_irreducible representation first second generates
    first_square second_square
  exact finrank_le_two_of_scalar_anticommutator representation first second generates first_square second_square
    scalar scalar_eq first_nonzero

end CFSG.OrderReductions.QuadraticDimension
