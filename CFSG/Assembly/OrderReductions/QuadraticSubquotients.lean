module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.OrderReductions.QuadraticSubquotients

theorem restriction_quadratic {field vector actors : Type*} [Field field]
    [AddCommGroup vector] [Module field vector] [Group actors]
    (representation : Representation field actors vector) (subspace : Submodule field vector)
    (invariant : ∀ actor, subspace ≤ subspace.comap (representation actor)) (actor : actors)
    (square_zero : (representation actor - 1) * (representation actor - 1) = 0) :
    let restricted := representation.subrepresentation subspace invariant
    (restricted actor - 1) * (restricted actor - 1) = 0 := by
  dsimp only
  apply LinearMap.ext
  intro element
  apply Subtype.ext
  exact congrArg (fun operator : Module.End field vector => operator element.val) square_zero

theorem quotient_apply_mk {field vector actors : Type*} [Field field]
    [AddCommGroup vector] [Module field vector] [Group actors]
    (representation : Representation field actors vector) (subspace : Submodule field vector)
    (invariant : ∀ actor, subspace ≤ subspace.comap (representation actor))
    (actor : actors) (element : vector) :
    (representation.quotient subspace invariant) actor (subspace.mkQ element) =
      subspace.mkQ (representation actor element) := by
  rw [Representation.quotient_apply]
  rfl

theorem quotient_quadratic {field vector actors : Type*} [Field field]
    [AddCommGroup vector] [Module field vector] [Group actors]
    (representation : Representation field actors vector) (subspace : Submodule field vector)
    (invariant : ∀ actor, subspace ≤ subspace.comap (representation actor)) (actor : actors)
    (square_zero : (representation actor - 1) * (representation actor - 1) = 0) :
    let quotient := representation.quotient subspace invariant
    (quotient actor - 1) * (quotient actor - 1) = 0 := by
  dsimp only
  apply LinearMap.ext
  intro element
  obtain ⟨original, rfl⟩ := subspace.mkQ_surjective element
  have original_zero := congrArg (fun operator : Module.End field vector => operator original) square_zero
  have mapped_zero := congrArg subspace.mkQ original_zero
  simpa only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
    quotient_apply_mk, ← map_sub, LinearMap.zero_apply, map_zero] using mapped_zero

theorem square_zero_of_subspace_quotient_identity {field vector actors : Type*} [Field field]
    [AddCommGroup vector] [Module field vector] [Group actors]
    (representation : Representation field actors vector) (subspace : Submodule field vector)
    (invariant : ∀ actor, subspace ≤ subspace.comap (representation actor)) (actor : actors)
    (restriction_identity : (representation.subrepresentation subspace invariant) actor = 1)
    (quotient_identity : (representation.quotient subspace invariant) actor = 1) :
    (representation actor - 1) * (representation actor - 1) = 0 := by
  have fixes_subspace : ∀ element ∈ subspace, representation actor element = element := by
    intro element membership
    exact congrArg (fun operator : Module.End field subspace => (operator ⟨element, membership⟩).val)
      restriction_identity
  have difference_mem : ∀ element : vector, representation actor element - element ∈ subspace := by
    intro element
    apply (Submodule.Quotient.eq subspace).mp
    have fixes := congrArg (fun operator : Module.End field (vector ⧸ subspace) =>
      operator (subspace.mkQ element)) quotient_identity
    rw [quotient_apply_mk] at fixes
    exact fixes
  ext element
  change representation actor (representation actor element - element) -
    (representation actor element - element) = 0
  exact sub_eq_zero.mpr (fixes_subspace _ (difference_mem element))

theorem pow_prime_eq_one_of_square_zero {ring : Type*} [Ring ring] (prime : ℕ)
    [Fact (Nat.Prime prime)] [CharP ring prime] (element : ring)
    (square_zero : (element - 1) * (element - 1) = 0) : element ^ prime = 1 := by
  have difference_pow : (element - 1) ^ prime = 0 := by
    obtain ⟨exponent, exponent_eq⟩ := Nat.exists_eq_add_of_le (Fact.out : Nat.Prime prime).two_le
    rw [exponent_eq, pow_add]
    rw [pow_two, square_zero, zero_mul]
  have binomial := add_pow_char_of_commute (R := ring) prime (Commute.one_left (element - 1))
  simpa only [add_sub_cancel, one_pow, difference_pow, add_zero] using binomial

end CFSG.OrderReductions.QuadraticSubquotients
