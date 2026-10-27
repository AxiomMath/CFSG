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
public import CFSG.Assembly.OrderReductions.CoprimeFixedSubgroup

public section

namespace CFSG.OrderReductions.OddInversion

abbrev InvertedElements {group : Type*} [Group group] (automorphism : MulAut group) :=
  {element : group // automorphism element = element⁻¹}

@[expose] def fixedSubgroup {group : Type*} [Group group] (automorphism : MulAut group) : Subgroup group :=
  automorphism.toMonoidHom.eqLocus (MonoidHom.id group)

@[expose, instance_reducible] def twistedAction {group : Type*} [Group group] (automorphism : MulAut group)
    (involutive : Function.Involutive automorphism) :
    MulAction group (InvertedElements automorphism) where
  smul conjugator element :=
    ⟨conjugator * element.val * (automorphism conjugator)⁻¹, by
      rw [map_mul, map_mul, map_inv, involutive, element.property, mul_inv_rev, mul_inv_rev, inv_inv]
      group⟩
  one_smul element := by
    apply Subtype.ext
    change 1 * element.val * (automorphism 1)⁻¹ = element.val
    simp only [map_one, inv_one, one_mul, mul_one]
  mul_smul first second element := by
    apply Subtype.ext
    change (first * second) * element.val * (automorphism (first * second))⁻¹ =
      first * (second * element.val * (automorphism second)⁻¹) * (automorphism first)⁻¹
    rw [map_mul, mul_inv_rev]
    group

theorem inverted_exists_commutator {group : Type*} [Group group]
    (automorphism : MulAut group) (element : InvertedElements automorphism)
    (odd_order : Odd (orderOf element.val)) :
    ∃ conjugator : group, conjugator * (automorphism conjugator)⁻¹ = element.val := by
  obtain ⟨half, order_eq⟩ := odd_order
  refine ⟨element.val ^ (half + 1), ?_⟩
  rw [map_pow, element.property, inv_pow, inv_inv, ← pow_add]
  have exponent_eq : half + 1 + (half + 1) = orderOf element.val + 1 := by omega
  rw [exponent_eq, pow_succ, pow_orderOf_eq_one, one_mul]

theorem inverted_action_pretransitive {group : Type*} [Group group]
    (automorphism : MulAut group) (involutive : Function.Involutive automorphism)
    (odd_order : Odd (Nat.card group)) :
    let action := twistedAction automorphism involutive
    @MulAction.IsPretransitive group (InvertedElements automorphism) action.toSMul := by
  let := twistedAction automorphism involutive
  let identity : InvertedElements automorphism := ⟨1, by simp⟩
  apply (MulAction.isPretransitive_iff_base identity).mpr
  intro element
  obtain ⟨conjugator, equal_element⟩ := inverted_exists_commutator automorphism element
    (odd_order.of_dvd_nat (orderOf_dvd_natCard element.val))
  refine ⟨conjugator, ?_⟩
  apply Subtype.ext
  change conjugator * 1 * (automorphism conjugator)⁻¹ = element.val
  simpa only [mul_one] using equal_element

theorem identity_stabilizer_eq_fixedSubgroup {group : Type*} [Group group]
    (automorphism : MulAut group) (involutive : Function.Involutive automorphism) :
    let action := twistedAction automorphism involutive
    let identity : InvertedElements automorphism := ⟨1, by simp⟩
    @MulAction.stabilizer group (InvertedElements automorphism) _ action identity =
      fixedSubgroup automorphism := by
  let := twistedAction automorphism involutive
  let identity : InvertedElements automorphism := ⟨1, by simp⟩
  ext element
  change element • identity = identity ↔ automorphism element = element
  rw [Subtype.ext_iff]
  change element * 1 * (automorphism element)⁻¹ = 1 ↔ automorphism element = element
  rw [mul_one, mul_inv_eq_one]
  exact eq_comm

theorem inverted_card_eq_fixed_index {group : Type*} [Group group] [Finite group]
    (automorphism : MulAut group) (involutive : Function.Involutive automorphism)
    (odd_order : Odd (Nat.card group)) :
    Nat.card (InvertedElements automorphism) = (fixedSubgroup automorphism).index := by
  let := twistedAction automorphism involutive
  have := inverted_action_pretransitive automorphism involutive odd_order
  let identity : InvertedElements automorphism := ⟨1, by simp⟩
  rw [← identity_stabilizer_eq_fixedSubgroup automorphism involutive,
    MulAction.index_stabilizer, MulAction.orbit_eq_univ, Set.ncard_univ]

theorem inverted_card_mul_fixed_card {group : Type*} [Group group] [Finite group]
    (automorphism : MulAut group) (involutive : Function.Involutive automorphism)
    (odd_order : Odd (Nat.card group)) :
    Nat.card (InvertedElements automorphism) * Nat.card (fixedSubgroup automorphism) =
      Nat.card group := by
  rw [inverted_card_eq_fixed_index automorphism involutive odd_order, mul_comm]
  exact (fixedSubgroup automorphism).card_mul_index

end CFSG.OrderReductions.OddInversion
