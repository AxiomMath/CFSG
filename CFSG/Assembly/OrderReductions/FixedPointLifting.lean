module

public import Mathlib
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.TensorProduct.Finite

public section

namespace CFSG.OrderReductions.FixedPointLifting

@[expose, instance_reducible] def fiberAction {actor source target : Type*}
    [Group actor] [Group source] [Group target]
    (source_action : actor →* MulAut source) (target_action : actor →* MulAut target)
    (homomorphism : source →* target)
    (equivariant : ∀ acting : actor, ∀ element : source,
      homomorphism (source_action acting element) = target_action acting (homomorphism element))
    (point : target) (fixed : ∀ acting : actor, target_action acting point = point) :
    MulAction actor {element : source // homomorphism element = point} where
  smul acting element := ⟨source_action acting element.val, by
    rw [equivariant, element.property, fixed]⟩
  one_smul element := by
    apply Subtype.ext
    change source_action 1 element.val = element.val
    rw [map_one]
    rfl
  mul_smul first second element := by
    apply Subtype.ext
    change source_action (first * second) element.val =
      source_action first (source_action second element.val)
    rw [map_mul]
    rfl

theorem exists_fixed_lift_of_coprime_kernel {actor source target : Type*}
    [Group actor] [Group source] [Group target] [Finite source]
    (prime : ℕ) [Fact (Nat.Prime prime)] (prime_actor : IsPGroup prime actor)
    (source_action : actor →* MulAut source) (target_action : actor →* MulAut target)
    (homomorphism : source →* target) (surjective : Function.Surjective homomorphism)
    (kernel_coprime : ¬ prime ∣ Nat.card homomorphism.ker)
    (equivariant : ∀ acting : actor, ∀ element : source,
      homomorphism (source_action acting element) = target_action acting (homomorphism element))
    (point : target) (fixed : ∀ acting : actor, target_action acting point = point) :
    ∃ element : source, homomorphism element = point ∧
      ∀ acting : actor, source_action acting element = element := by
  let := fiberAction source_action target_action homomorphism equivariant point fixed
  have fiber_card : Nat.card {element : source // homomorphism element = point} =
      Nat.card homomorphism.ker := by
    exact Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective surjective point)
  have fiber_coprime : ¬ prime ∣ Nat.card {element : source // homomorphism element = point} := by
    rwa [fiber_card]
  obtain ⟨element, element_fixed⟩ := prime_actor.nonempty_fixed_point_of_prime_not_dvd_card
    {element : source // homomorphism element = point} fiber_coprime
  refine ⟨element.val, element.property, ?_⟩
  intro acting
  exact congrArg Subtype.val (MulAction.mem_fixedPoints.mp element_fixed acting)

theorem exists_fixed_lift_of_coprime {actor source target : Type*}
    [Group actor] [Group source] [Group target] [Finite source]
    (prime : ℕ) [Fact (Nat.Prime prime)] (prime_actor : IsPGroup prime actor)
    (source_action : actor →* MulAut source) (target_action : actor →* MulAut target)
    (homomorphism : source →* target) (surjective : Function.Surjective homomorphism)
    (coprime : ¬ prime ∣ Nat.card source)
    (equivariant : ∀ acting : actor, ∀ element : source,
      homomorphism (source_action acting element) = target_action acting (homomorphism element))
    (point : target) (fixed : ∀ acting : actor, target_action acting point = point) :
    ∃ element : source, homomorphism element = point ∧
      ∀ acting : actor, source_action acting element = element := by
  exact exists_fixed_lift_of_coprime_kernel prime prime_actor source_action target_action
    homomorphism surjective (fun divides =>
      coprime (divides.trans homomorphism.ker.card_subgroup_dvd_card)) equivariant point fixed

theorem exists_fixed_lift_of_odd_kernel {source target : Type*}
    [Group source] [Group target] [Finite source]
    (source_automorphism : MulAut source) (target_automorphism : MulAut target)
    (involutive : Function.Involutive source_automorphism)
    (homomorphism : source →* target) (surjective : Function.Surjective homomorphism)
    (odd_kernel : Odd (Nat.card homomorphism.ker))
    (equivariant : ∀ element : source,
      homomorphism (source_automorphism element) = target_automorphism (homomorphism element))
    (point : target) (fixed : target_automorphism point = point) :
    ∃ element : source, homomorphism element = point ∧ source_automorphism element = element := by
  classical
  let fiber := {element : source // homomorphism element = point}
  let permutation : Equiv.Perm fiber :=
    { toFun := fun element => ⟨source_automorphism element.val, by
        rw [equivariant, element.property, fixed]⟩
      invFun := fun element => ⟨source_automorphism element.val, by
        rw [equivariant, element.property, fixed]⟩
      left_inv := fun element => Subtype.ext (involutive element.val)
      right_inv := fun element => Subtype.ext (involutive element.val) }
  let := Fintype.ofFinite fiber
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  have permutation_square : permutation ^ (2 ^ 1) = 1 := by
    ext element
    exact involutive element.val
  have fiber_card : Nat.card fiber = Nat.card homomorphism.ker :=
    Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective surjective point)
  have not_divides : ¬ 2 ∣ Fintype.card fiber := by
    rw [← Nat.card_eq_fintype_card, fiber_card]
    exact odd_kernel.not_two_dvd_nat
  obtain ⟨element, fixed_element⟩ :=
    Equiv.Perm.exists_fixed_point_of_prime not_divides permutation_square
  exact ⟨element.val, element.property, congrArg Subtype.val fixed_element⟩

end CFSG.OrderReductions.FixedPointLifting
