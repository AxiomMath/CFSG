module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.OrderReductions.TwoDimensionalScalars

attribute [local instance] commutatorElement

@[expose] def scalarImage {field vector actors : Type*} [Field field] [AddCommGroup vector]
    [Module field vector] [Group actors] (representation : Representation field actors vector)
    (actor : actors) : Prop := ∃ scalar : field, representation actor = scalar • (1 : Module.End field vector)

theorem scalar_commutator_trivial {field vector actors : Type*} [Field field]
    [AddCommGroup vector] [Module field vector] [FiniteDimensional field vector]
    [Group actors] [Finite actors] (representation : Representation field actors vector)
    (dimension : Module.finrank field vector = 2) (odd_order : Odd (Nat.card actors))
    (first second : actors) (scalar : scalarImage representation ⁅first, second⁆) :
    representation ⁅first, second⁆ = 1 := by
  obtain ⟨value, scalar_eq⟩ := scalar
  let determinant := (Units.map (LinearMap.det : Module.End field vector →* field)).comp
    representation.asGroupHom
  have determinant_one : determinant ⁅first, second⁆ = 1 := by
    simp only [commutatorElement_def, map_mul, map_inv]
    rw [mul_right_comm (determinant first) (determinant second) (determinant first)⁻¹,
      mul_inv_cancel, one_mul, mul_inv_cancel]
  have scalar_square : value ^ 2 = 1 := by
    have equal := congrArg (fun unit : fieldˣ => unit.val) determinant_one
    change LinearMap.det (representation ⁅first, second⁆) = 1 at equal
    rwa [scalar_eq, LinearMap.det_smul, dimension, map_one, mul_one] at equal
  have scalar_pow : value ^ Nat.card actors = 1 := by
    have operator_pow : representation ⁅first, second⁆ ^ Nat.card actors = 1 := by
      rw [← map_pow, pow_card_eq_one', map_one]
    rw [scalar_eq] at operator_pow
    have nontrivial_vector : Nontrivial vector := by
      apply Module.nontrivial_of_finrank_pos (R := field)
      omega
    obtain ⟨element, element_ne⟩ := exists_ne (0 : vector)
    have fixed := congrArg (fun linear : Module.End field vector => linear element) operator_pow
    have powered : (value • (1 : Module.End field vector)) ^ Nat.card actors =
        value ^ Nat.card actors • (1 : Module.End field vector) := by
      simp only [smul_pow, one_pow]
    rw [powered] at fixed
    change value ^ Nat.card actors • element = element at fixed
    exact smul_left_injective field element_ne (fixed.trans (one_smul field element).symm)
  have value_one : value = 1 := by
    rcases (sq_eq_one_iff.mp scalar_square) with equal | equal
    · exact equal
    · rw [equal, odd_order.neg_one_pow] at scalar_pow
      exact equal.trans scalar_pow
  rw [scalar_eq, value_one, one_smul]

theorem subgroup_image_commutative_of_scalar_derived {field vector actors : Type*} [Field field]
    [AddCommGroup vector] [Module field vector] [FiniteDimensional field vector]
    [Group actors] [Finite actors] (representation : Representation field actors vector)
    (dimension : Module.finrank field vector = 2) (odd_order : Odd (Nat.card actors))
    (subgroup : Subgroup actors)
    (scalar_derived : ∀ actor ∈ ⁅subgroup, subgroup⁆, scalarImage representation actor)
    (first second : subgroup) : Commute (representation first.val) (representation second.val) := by
  have commutator_mem := Subgroup.commutator_mem_commutator first.property second.property
  have commutator_one := scalar_commutator_trivial representation dimension odd_order first.val second.val
    (scalar_derived _ commutator_mem)
  have unit_one : representation.asGroupHom ⁅first.val, second.val⁆ = 1 := Units.ext commutator_one
  have commutes : Commute (representation.asGroupHom first.val) (representation.asGroupHom second.val) := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rwa [map_commutatorElement] at unit_one
  exact commutes.units_val

theorem exists_normal_commutative_image_nonscalar {field vector actors : Type*} [Field field]
    [AddCommGroup vector] [Module field vector] [FiniteDimensional field vector]
    [Group actors] [Finite actors] [Group.IsSolvable actors]
    (representation : Representation field actors vector)
    (dimension : Module.finrank field vector = 2) (odd_order : Odd (Nat.card actors))
    (nonscalar : ∃ actor : actors, ¬ scalarImage representation actor) :
    ∃ normal : Subgroup actors, normal.Normal ∧
      (∀ first second : normal, Commute (representation first.val) (representation second.val)) ∧
      ∃ actor : normal, ¬ scalarImage representation actor.val := by
  obtain ⟨bound, derived_bot⟩ := (Group.isSolvable_def actors).mp inferInstance
  have descend : ∀ distance depth, depth + distance = bound →
      (∀ actor ∈ derivedSeries actors depth, scalarImage representation actor) ∨
      ∃ normal : Subgroup actors, normal.Normal ∧
        (∀ first second : normal, Commute (representation first.val) (representation second.val)) ∧
        ∃ actor : normal, ¬ scalarImage representation actor.val := by
    intro distance
    induction distance with
    | zero =>
        intro depth equation
        left
        have depth_eq : depth = bound := by omega
        rw [depth_eq, derived_bot]
        intro actor actor_mem
        rw [Subgroup.mem_bot.mp actor_mem]
        exact ⟨1, by rw [map_one, one_smul]⟩
    | succ distance induction_hypothesis =>
        intro depth equation
        rcases induction_hypothesis (depth + 1) (by omega) with next_scalar | result
        · by_cases all_scalar : ∀ actor ∈ derivedSeries actors depth, scalarImage representation actor
          · exact Or.inl all_scalar
          · right
            push Not at all_scalar
            obtain ⟨actor, membership, not_scalar⟩ := all_scalar
            refine ⟨derivedSeries actors depth, inferInstance, ?_, ⟨⟨actor, membership⟩, not_scalar⟩⟩
            apply subgroup_image_commutative_of_scalar_derived representation dimension odd_order
            rwa [← derivedSeries_succ]
        · exact Or.inr result
  rcases descend bound 0 (by omega) with all_scalar | result
  · obtain ⟨actor, not_scalar⟩ := nonscalar
    apply False.elim
    exact not_scalar (all_scalar actor (derivedSeries_zero actors ▸ Subgroup.mem_top actor))
  · exact result

end CFSG.OrderReductions.TwoDimensionalScalars
