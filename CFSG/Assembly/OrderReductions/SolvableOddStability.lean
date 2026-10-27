module

public import CFSG.Assembly.OrderReductions.ActionImageCore
public import CFSG.Assembly.OrderReductions.ElementaryRepresentation
public import CFSG.Assembly.OrderReductions.LinearPrimeStability

public section

namespace CFSG.OrderReductions.SolvableOddStability

open CFSG.OrderReductions.ActionPrimeCore CFSG.OrderReductions.ActionImageCore CFSG.OrderReductions.ElementaryRepresentation

theorem linearRepresentation_injective {actors target : Type*} [Group actors] [CommGroup target]
    (prime : ℕ) [Module (ZMod prime) (Additive target)] (action : actors →* MulAut target)
    (faithful : Function.Injective action) : Function.Injective (linearRepresentation prime action) := by
  intro first second equal
  apply faithful
  ext element
  have fixed := congrArg (fun operator : Module.End (ZMod prime) (Additive target) =>
    operator (Additive.ofMul element)) equal
  exact congrArg Additive.toMul fixed

theorem elementary_primeStable_of_faithful {actors target : Type*} [Group actors] [Finite actors]
    [Group.IsSolvable actors] [CommGroup target] [Finite target]
    (prime : ℕ) [Fact (Nat.Prime prime)] [Module (ZMod prime) (Additive target)]
    (action : actors →* MulAut target) (odd_order : Odd (Nat.card actors))
    (faithful : Function.Injective action) : primeStable prime action := by
  intro actor quadratic_actor
  let representation := linearRepresentation prime action
  have inverse_square := (quadratic_iff_square_zero prime action actor).mp quadratic_actor
  have square_zero := CFSG.OrderReductions.LinearPrimeStability.inverse_quadratic representation actor⁻¹ inverse_square
  rw [inv_inv] at square_zero
  apply primeCore_le_actionCore prime action
  exact CFSG.OrderReductions.LinearPrimeStability.quadratic_mem_primeCore_of_faithful prime representation
    odd_order (linearRepresentation_injective prime action faithful) actor square_zero

theorem elementary_primeStable {actors target : Type*} [Group actors] [Finite actors]
    [Group.IsSolvable actors] [CommGroup target] [Finite target]
    (prime : ℕ) [Fact (Nat.Prime prime)] [Module (ZMod prime) (Additive target)]
    (action : actors →* MulAut target) (odd_order : Odd (Nat.card actors)) : primeStable prime action := by
  have : Group.IsSolvable action.range := Group.isSolvable_of_surjective action.rangeRestrict_surjective
  apply primeStable_of_range_action prime action
  exact elementary_primeStable_of_faithful prime action.range.subtype
    (odd_order.of_dvd_nat (Subgroup.card_range_dvd action)) Subtype.val_injective

theorem primeStable_of_solvable_odd {actors target : Type*} [Group actors] [Finite actors]
    [Group.IsSolvable actors] [Group target] [Finite target]
    (prime : ℕ) [Fact (Nat.Prime prime)] (prime_target : IsPGroup prime target)
    (action : actors →* MulAut target) (odd_order : Odd (Nat.card actors)) : primeStable prime action := by
  apply primeStable_of_frattini_quotient_image prime prime_target action
  have : Group.IsSolvable action.range := Group.isSolvable_of_surjective action.rangeRestrict_surjective
  let := frattiniQuotientCommGroup prime prime_target
  let := frattiniQuotientModule prime prime_target
  exact elementary_primeStable prime
    (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAction (frattini target) action.range.subtype)
    (odd_order.of_dvd_nat (Subgroup.card_range_dvd action))

end CFSG.OrderReductions.SolvableOddStability
