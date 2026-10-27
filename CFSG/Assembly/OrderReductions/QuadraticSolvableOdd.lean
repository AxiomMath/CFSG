module

public import CFSG.Assembly.OrderReductions.QuadraticIrreducibleOdd
public import CFSG.Assembly.OrderReductions.QuadraticSubquotients

public section

namespace CFSG.OrderReductions.QuadraticSolvableOdd

theorem exists_proper_invariant_subspace {field vector actors : Type*} [Field field]
    [AddCommGroup vector] [Module field vector] [Group actors] [Nontrivial vector]
    (representation : Representation field actors vector)
    (reducible : ¬ representation.IsIrreducible) :
    ∃ subspace : Submodule field vector, subspace ≠ ⊥ ∧ subspace ≠ ⊤ ∧
      ∀ actor, subspace ≤ subspace.comap (representation actor) := by
  classical
  have : Nontrivial (Subrepresentation representation) :=
    nontrivial_of_ne (⊥ : Subrepresentation representation) ⊤ (by
      intro equal
      exact bot_ne_top (congrArg Subrepresentation.toSubmodule equal))
  have exists_subrepresentation : ∃ subrepresentation : Subrepresentation representation,
      subrepresentation ≠ ⊥ ∧ subrepresentation ≠ ⊤ := by
    by_contra none
    apply reducible
    apply (isSimpleOrder_iff _).mpr
    refine ⟨inferInstance, ?_⟩
    intro subrepresentation
    by_contra neither
    push Not at neither
    exact none ⟨subrepresentation, neither⟩
  obtain ⟨subrepresentation, not_bot, not_top⟩ := exists_subrepresentation
  refine ⟨subrepresentation.toSubmodule, ?_, ?_, ?_⟩
  · intro equal
    exact not_bot (Subrepresentation.ext equal)
  · intro equal
    exact not_top (Subrepresentation.ext equal)
  · intro actor element membership
    exact subrepresentation.apply_mem_toSubmodule actor membership

theorem exists_prime_power_identity {field vector actors : Type*} [Field field] [IsAlgClosed field]
    [AddCommGroup vector] [Module field vector] [FiniteDimensional field vector]
    [Group actors] [Finite actors] [Group.IsSolvable actors]
    (prime : ℕ) [Fact (Nat.Prime prime)] [CharP field prime]
    (representation : Representation field actors vector) (odd_order : Odd (Nat.card actors))
    (first second : actors) (generates : Subgroup.closure ({first, second} : Set actors) = ⊤)
    (first_square : (representation first - 1) * (representation first - 1) = 0)
    (second_square : (representation second - 1) * (representation second - 1) = 0) :
    ∀ actor : actors, ∃ exponent : ℕ, representation actor ^ (prime ^ exponent) = 1 := by
  classical
  generalize dimension_eq : Module.finrank field vector = dimension
  induction dimension using Nat.strong_induction_on generalizing vector with
  | h dimension induction_hypothesis =>
      by_cases nontrivial : Nontrivial vector
      · have : Nontrivial vector := nontrivial
        have : CharP (Module.End field vector) prime :=
          CharP.of_ringHom_of_ne_zero (algebraMap field (Module.End field vector)) prime
            (Fact.out : Nat.Prime prime).ne_zero
        by_cases irreducible : representation.IsIrreducible
        · have : representation.IsIrreducible := irreducible
          intro actor
          refine ⟨0, ?_⟩
          rw [pow_zero, pow_one]
          exact CFSG.OrderReductions.QuadraticIrreducibleOdd.irreducible_quadratic_odd_trivial
            representation odd_order first second generates first_square second_square actor
        · obtain ⟨subspace, not_bot, not_top, invariant⟩ :=
            exists_proper_invariant_subspace representation irreducible
          have subspace_smaller : Module.finrank field subspace < dimension := by
            rw [← dimension_eq]
            exact Submodule.finrank_lt not_top
          have subspace_positive : 0 < Module.finrank field subspace := by
            have : Nontrivial subspace := Submodule.nontrivial_iff_ne_bot.mpr not_bot
            exact Module.finrank_pos
          have quotient_smaller : Module.finrank field (vector ⧸ subspace) < dimension := by
            have dimensions := Submodule.finrank_quotient_add_finrank subspace
            omega
          have restriction_result := induction_hypothesis _ subspace_smaller
            (representation.subrepresentation subspace invariant)
            (CFSG.OrderReductions.QuadraticSubquotients.restriction_quadratic representation subspace invariant first first_square)
            (CFSG.OrderReductions.QuadraticSubquotients.restriction_quadratic representation subspace invariant second second_square) rfl
          have quotient_result := induction_hypothesis _ quotient_smaller
            (representation.quotient subspace invariant)
            (CFSG.OrderReductions.QuadraticSubquotients.quotient_quadratic representation subspace invariant first first_square)
            (CFSG.OrderReductions.QuadraticSubquotients.quotient_quadratic representation subspace invariant second second_square) rfl
          intro actor
          obtain ⟨restriction_exponent, restriction_pow⟩ := restriction_result actor
          obtain ⟨quotient_exponent, quotient_pow⟩ := quotient_result actor
          have restriction_common :
              (representation.subrepresentation subspace invariant) (actor ^ (prime ^ (restriction_exponent + quotient_exponent))) = 1 := by
            rw [map_pow, pow_add, pow_mul, restriction_pow, one_pow]
          have quotient_common :
              (representation.quotient subspace invariant) (actor ^ (prime ^ (restriction_exponent + quotient_exponent))) = 1 := by
            rw [map_pow, add_comm restriction_exponent quotient_exponent, pow_add, pow_mul, quotient_pow, one_pow]
          have powered_square := CFSG.OrderReductions.QuadraticSubquotients.square_zero_of_subspace_quotient_identity
            representation subspace invariant _ restriction_common quotient_common
          have powered_identity := CFSG.OrderReductions.QuadraticSubquotients.pow_prime_eq_one_of_square_zero prime
            (representation (actor ^ (prime ^ (restriction_exponent + quotient_exponent)))) powered_square
          refine ⟨restriction_exponent + quotient_exponent + 1, ?_⟩
          rwa [map_pow, ← pow_mul, ← pow_succ] at powered_identity
      · have : Subsingleton vector := not_nontrivial_iff_subsingleton.mp nontrivial
        intro actor
        refine ⟨0, ?_⟩
        apply LinearMap.ext
        intro element
        exact Subsingleton.elim _ _

end CFSG.OrderReductions.QuadraticSolvableOdd
