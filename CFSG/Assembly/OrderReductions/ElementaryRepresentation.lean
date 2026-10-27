module

public import CFSG.Assembly.OrderReductions.ActionPrimeCore
public import CFSG.Assembly.OrderReductions.FrattiniElementary

public section

namespace CFSG.OrderReductions.ElementaryRepresentation

open CFSG.OrderReductions.ActionPrimeCore CFSG.OrderReductions.ClassTwoCubic

@[expose] def linearRepresentation {actors target : Type*} [Group actors] [CommGroup target]
    (prime : ℕ) [Module (ZMod prime) (Additive target)] (action : actors →* MulAut target) :
    Representation (ZMod prime) actors (Additive target) where
  toFun actor := AddMonoidHom.toZModLinearMap prime
    (MonoidHom.toAdditive (action actor).toMonoidHom)
  map_one' := by
    ext element
    change Additive.ofMul (action 1 element.toMul) = element
    rw [map_one]
    rfl
  map_mul' first second := by
    ext element
    change Additive.ofMul (action (first * second) element.toMul) =
      Additive.ofMul (action first (action second element.toMul))
    rw [map_mul]
    rfl

theorem linearRepresentation_apply {actors target : Type*} [Group actors] [CommGroup target]
    (prime : ℕ) [Module (ZMod prime) (Additive target)] (action : actors →* MulAut target)
    (actor : actors) (element : Additive target) :
    linearRepresentation prime action actor element = Additive.ofMul (action actor element.toMul) := rfl

theorem linearRepresentation_kernel {actors target : Type*} [Group actors] [CommGroup target]
    (prime : ℕ) [Module (ZMod prime) (Additive target)] (action : actors →* MulAut target) :
    (linearRepresentation prime action).asGroupHom.ker = action.ker := by
  ext actor
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  · intro equal
    ext element
    have fixed := congrArg (fun unit : (Module.End (ZMod prime) (Additive target))ˣ =>
      (unit : Module.End (ZMod prime) (Additive target)) (Additive.ofMul element)) equal
    change Additive.ofMul (action actor element) = Additive.ofMul element at fixed
    exact congrArg Additive.toMul fixed
  · intro equal
    apply Units.ext
    ext element
    change Additive.ofMul (action actor element.toMul) = element
    rw [equal]
    rfl

theorem quadratic_iff_square_zero {actors target : Type*} [Group actors] [CommGroup target]
    (prime : ℕ) [Module (ZMod prime) (Additive target)] (action : actors →* MulAut target)
    (actor : actors) :
    quadratic action actor ↔
      (linearRepresentation prime action actor⁻¹ - 1) *
        (linearRepresentation prime action actor⁻¹ - 1) = 0 := by
  have difference_eq : ∀ element : target,
      (linearRepresentation prime action actor⁻¹ - 1) (Additive.ofMul element) =
        Additive.ofMul (difference (action actor⁻¹) element) := by
    intro element
    change Additive.ofMul (action actor⁻¹ element) - Additive.ofMul element =
      Additive.ofMul (element⁻¹ * action actor⁻¹ element)
    change Additive.ofMul (action actor⁻¹ element / element) = _
    rw [div_eq_mul_inv, mul_comm]
  constructor
  · intro quadratic_actor
    ext element
    change (linearRepresentation prime action actor⁻¹ - 1)
      ((linearRepresentation prime action actor⁻¹ - 1) element) = 0
    change (linearRepresentation prime action actor⁻¹ - 1)
      ((linearRepresentation prime action actor⁻¹ - 1) (Additive.ofMul element.toMul)) = 0
    rw [difference_eq, difference_eq, quadratic_actor]
    rfl
  · intro square_zero element
    have equal := congrArg (fun linear : Module.End (ZMod prime) (Additive target) =>
      linear (Additive.ofMul element)) square_zero
    change (linearRepresentation prime action actor⁻¹ - 1)
      ((linearRepresentation prime action actor⁻¹ - 1) (Additive.ofMul element)) = 0 at equal
    rw [difference_eq, difference_eq] at equal
    exact congrArg Additive.toMul equal

@[expose, instance_reducible] def exponentModule {target : Type*} [CommGroup target] (prime : ℕ)
    (exponent : ∀ element : target, element ^ prime = 1) : Module (ZMod prime) (Additive target) :=
  AddCommGroup.zmodModule (n := prime) (fun element => by
    change Additive.ofMul (element.toMul ^ prime) = 0
    rw [exponent]
    rfl)

@[expose, instance_reducible] noncomputable def frattiniQuotientCommGroup {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (prime_group : IsPGroup prime group) :
    CommGroup (group ⧸ frattini group) :=
  (CFSG.OrderReductions.FrattiniElementary.frattini_quotient_isMulCommutative prime prime_group).instCommGroup

@[expose, instance_reducible] noncomputable def frattiniQuotientModule {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (prime_group : IsPGroup prime group) :
    letI := frattiniQuotientCommGroup prime prime_group
    Module (ZMod prime) (Additive (group ⧸ frattini group)) := by
  letI := frattiniQuotientCommGroup prime prime_group
  exact exponentModule prime (CFSG.OrderReductions.FrattiniElementary.frattini_quotient_exponent prime prime_group)

end CFSG.OrderReductions.ElementaryRepresentation
