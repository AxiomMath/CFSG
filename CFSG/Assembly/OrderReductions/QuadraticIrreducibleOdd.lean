module

public import CFSG.Assembly.OrderReductions.QuadraticDimension
public import CFSG.Assembly.OrderReductions.TwoDimensionalOdd

public section

namespace CFSG.OrderReductions.QuadraticIrreducibleOdd

theorem square_zero_nonzero_finrank_ge_two {field vector : Type*} [Field field]
    [AddCommGroup vector] [Module field vector] [FiniteDimensional field vector]
    (operator : Module.End field vector) (square_zero : operator * operator = 0)
    (nonzero : operator ≠ 0) : 2 ≤ Module.finrank field vector := by
  classical
  have exists_nonzero : ∃ original : vector, operator original ≠ 0 := by
    by_contra none
    push Not at none
    exact nonzero (LinearMap.ext none)
  obtain ⟨original, original_nonzero⟩ := exists_nonzero
  have fixed_zero : operator (operator original) = 0 :=
    congrArg (fun linear : Module.End field vector => linear original) square_zero
  have independent : LinearIndependent field ![operator original, original] := by
    apply (LinearIndependent.pair_iff' original_nonzero).mpr
    intro scalar equal
    have applied := congrArg operator equal
    rw [map_smul, fixed_zero, smul_zero] at applied
    exact original_nonzero applied.symm
  simpa using independent.fintype_card_le_finrank

theorem generators_trivial_of_quadratic_irreducible_odd {field vector actors : Type*} [Field field]
    [IsAlgClosed field] [AddCommGroup vector] [Module field vector] [FiniteDimensional field vector]
    [Group actors] [Finite actors] [Group.IsSolvable actors]
    (representation : Representation field actors vector) [representation.IsIrreducible]
    (odd_order : Odd (Nat.card actors)) (first second : actors)
    (generates : Subgroup.closure ({first, second} : Set actors) = ⊤)
    (first_square : (representation first - 1) * (representation first - 1) = 0)
    (second_square : (representation second - 1) * (representation second - 1) = 0) :
    representation first = 1 ∧ representation second = 1 := by
  have first_trivial : representation first = 1 := by
    by_contra nontrivial
    have nonzero : representation first - 1 ≠ 0 := sub_ne_zero.mpr nontrivial
    have upper := CFSG.OrderReductions.QuadraticDimension.finrank_le_two_of_quadratic_irreducible representation
      first second generates first_square second_square nonzero
    have lower := square_zero_nonzero_finrank_ge_two (representation first - 1) first_square nonzero
    have dimension := le_antisymm upper lower
    exact CFSG.OrderReductions.TwoDimensionalOdd.not_irreducible_of_dimension_two_solvable_odd
      representation dimension odd_order inferInstance
  have second_trivial : representation second = 1 := by
    by_contra nontrivial
    have nonzero : representation second - 1 ≠ 0 := sub_ne_zero.mpr nontrivial
    have reverse_generates : Subgroup.closure ({second, first} : Set actors) = ⊤ := by
      simpa only [Set.pair_comm] using generates
    have upper := CFSG.OrderReductions.QuadraticDimension.finrank_le_two_of_quadratic_irreducible representation
      second first reverse_generates second_square first_square nonzero
    have lower := square_zero_nonzero_finrank_ge_two (representation second - 1) second_square nonzero
    have dimension := le_antisymm upper lower
    exact CFSG.OrderReductions.TwoDimensionalOdd.not_irreducible_of_dimension_two_solvable_odd
      representation dimension odd_order inferInstance
  exact ⟨first_trivial, second_trivial⟩

theorem irreducible_quadratic_odd_trivial {field vector actors : Type*} [Field field]
    [IsAlgClosed field] [AddCommGroup vector] [Module field vector] [FiniteDimensional field vector]
    [Group actors] [Finite actors] [Group.IsSolvable actors]
    (representation : Representation field actors vector) [representation.IsIrreducible]
    (odd_order : Odd (Nat.card actors)) (first second : actors)
    (generates : Subgroup.closure ({first, second} : Set actors) = ⊤)
    (first_square : (representation first - 1) * (representation first - 1) = 0)
    (second_square : (representation second - 1) * (representation second - 1) = 0) :
    ∀ actor : actors, representation actor = 1 := by
  obtain ⟨first_trivial, second_trivial⟩ := generators_trivial_of_quadratic_irreducible_odd
    representation odd_order first second generates first_square second_square
  intro actor
  have membership : actor ∈ Subgroup.closure ({first, second} : Set actors) := generates ▸ Subgroup.mem_top actor
  apply Subgroup.closure_induction'' (p := fun member _ => representation member = 1) ?_ ?_ ?_ ?_ membership
  · intro member member_mem
    rcases member_mem with (rfl | rfl)
    · exact first_trivial
    · exact second_trivial
  · intro member member_mem
    have forward : representation member = 1 := by
      rcases member_mem with (rfl | rfl)
      · exact first_trivial
      · exact second_trivial
    have inverse := CFSG.OrderReductions.QuadraticDimension.representation_inverse_square_zero representation member
      (by rw [forward, sub_self, zero_mul])
    rwa [forward, sub_self, sub_zero] at inverse
  · exact map_one representation
  · intro left right _ _ left_trivial right_trivial
    rw [map_mul, left_trivial, right_trivial, mul_one]

end CFSG.OrderReductions.QuadraticIrreducibleOdd
