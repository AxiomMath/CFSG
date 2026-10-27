module

public import CFSG.Assembly.OrderReductions.RepresentationScalarExtension
public import CFSG.Assembly.OrderReductions.SolvableConjugatePairs

public section

namespace CFSG.OrderReductions.LinearPrimeStability

open CFSG.OrderReductions.PrimeCore CFSG.OrderReductions.SolvableConjugatePairs

theorem inverse_quadratic {field vector actors : Type*} [Field field] [AddCommGroup vector]
    [Module field vector] [Group actors] (representation : Representation field actors vector)
    (actor : actors) (square_zero : (representation actor - 1) * (representation actor - 1) = 0) :
    (representation actor⁻¹ - 1) * (representation actor⁻¹ - 1) = 0 := by
  rw [CFSG.OrderReductions.QuadraticDimension.representation_inverse_square_zero representation actor square_zero]
  have difference : 1 - (representation actor - 1) - 1 = -(representation actor - 1) := by abel
  rw [difference, neg_mul_neg, square_zero]

theorem conjugate_quadratic {field vector actors : Type*} [Field field] [AddCommGroup vector]
    [Module field vector] [Group actors] (representation : Representation field actors vector)
    (actor conjugator : actors)
    (square_zero : (representation actor - 1) * (representation actor - 1) = 0) :
    (representation (conjugator⁻¹ * actor * conjugator) - 1) *
      (representation (conjugator⁻¹ * actor * conjugator) - 1) = 0 := by
  have difference : representation (conjugator⁻¹ * actor * conjugator) - 1 =
      representation conjugator⁻¹ * (representation actor - 1) * representation conjugator := by
    have inverse : representation conjugator⁻¹ * representation conjugator = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    simp only [map_mul]
    rw [mul_sub, sub_mul, mul_one, inverse]
  rw [difference]
  calc
    (representation conjugator⁻¹ * (representation actor - 1) * representation conjugator) *
        (representation conjugator⁻¹ * (representation actor - 1) * representation conjugator) =
      representation conjugator⁻¹ * ((representation actor - 1) *
        (representation conjugator * representation conjugator⁻¹) * (representation actor - 1)) *
        representation conjugator := by noncomm_ring
    _ = 0 := by
      rw [← map_mul, mul_inv_cancel, map_one, mul_one, square_zero, mul_zero, zero_mul]

theorem range_isPGroup_of_quadratic_generators {field vector actors : Type*} [Field field]
    [AddCommGroup vector] [Module field vector] [FiniteDimensional field vector]
    [Group actors] [Finite actors] [Group.IsSolvable actors]
    (prime : ℕ) [Fact (Nat.Prime prime)] [CharP field prime]
    (representation : Representation field actors vector) (odd_order : Odd (Nat.card actors))
    (first second : actors) (generates : Subgroup.closure ({first, second} : Set actors) = ⊤)
    (first_square : (representation first - 1) * (representation first - 1) = 0)
    (second_square : (representation second - 1) * (representation second - 1) = 0) :
    IsPGroup prime representation.asGroupHom.range := by
  apply isPGroup_iff_pow_pow_eq_one.mpr
  intro element
  obtain ⟨actor, rfl⟩ := representation.asGroupHom.rangeRestrict_surjective element
  obtain ⟨exponent, powered⟩ := CFSG.OrderReductions.RepresentationScalarExtension.exists_prime_power_identity
    prime representation odd_order first second generates first_square second_square actor
  refine ⟨exponent, ?_⟩
  apply Subtype.ext
  apply Units.ext
  exact powered

theorem conjugatePair_isPGroup_of_faithful_quadratic {field vector actors : Type*} [Field field]
    [AddCommGroup vector] [Module field vector] [FiniteDimensional field vector]
    [Group actors] [Finite actors] [Group.IsSolvable actors]
    (prime : ℕ) [Fact (Nat.Prime prime)] [CharP field prime]
    (representation : Representation field actors vector) (odd_order : Odd (Nat.card actors))
    (faithful : Function.Injective representation) (actor conjugator : actors)
    (square_zero : (representation actor - 1) * (representation actor - 1) = 0) :
    IsPGroup prime (conjugatePair actor conjugator) := by
  let paired := conjugatePair actor conjugator
  let first : paired := ⟨actor, Subgroup.subset_closure (by simp)⟩
  let second : paired := ⟨conjugator⁻¹ * actor * conjugator, Subgroup.subset_closure (by simp)⟩
  let restricted : Representation field paired vector := representation.comp paired.subtype
  have generates : Subgroup.closure ({first, second} : Set paired) = ⊤ := by
    have preimage : paired.subtype ⁻¹' ({actor, conjugator⁻¹ * actor * conjugator} : Set actors) =
        ({first, second} : Set paired) := by
      ext element
      simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro membership
        rcases membership with equal | equal
        · exact Or.inl (Subtype.ext equal)
        · exact Or.inr (Subtype.ext equal)
      · intro membership
        rcases membership with equal | equal
        · exact Or.inl (congrArg Subtype.val equal)
        · exact Or.inr (congrArg Subtype.val equal)
    rw [← preimage]
    exact Subgroup.closure_preimage_eq_top _
  have range_prime := range_isPGroup_of_quadratic_generators prime restricted
    (odd_order.of_dvd_nat paired.card_subgroup_dvd_card) first second generates square_zero
    (conjugate_quadratic representation actor conjugator square_zero)
  apply range_prime.of_injective restricted.asGroupHom.rangeRestrict
  intro first_member second_member equal
  apply Subtype.ext
  apply faithful
  exact congrArg (fun member : restricted.asGroupHom.range =>
    (member.val : Module.End field vector)) equal

theorem quadratic_mem_primeCore_of_faithful {field vector actors : Type*} [Field field]
    [AddCommGroup vector] [Module field vector] [FiniteDimensional field vector]
    [Group actors] [Finite actors] [Group.IsSolvable actors]
    (prime : ℕ) [Fact (Nat.Prime prime)] [CharP field prime]
    (representation : Representation field actors vector) (odd_order : Odd (Nat.card actors))
    (faithful : Function.Injective representation) (actor : actors)
    (square_zero : (representation actor - 1) * (representation actor - 1) = 0) :
    actor ∈ primeCore prime actors := by
  have pairs := conjugatePair_isPGroup_of_faithful_quadratic prime representation odd_order faithful actor
    (square_zero := square_zero)
  have prime_element : IsPGroup prime (Subgroup.zpowers actor) :=
    (pairs 1).to_le (Subgroup.zpowers_le_of_mem (Subgroup.subset_closure (by simp)))
  exact mem_primeCore_of_conjugate_pairs prime actor prime_element pairs

end CFSG.OrderReductions.LinearPrimeStability
