module

public import Mathlib
public import CFSG.Assembly.OrderReductions.StrongEmbedding
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
public import CFSG.Assembly.OrderReductions.FixedPairSylow

public section

namespace CFSG.OrderReductions.FixedConjugator

open scoped Pointwise

abbrev Transporters {group points : Type*} [Group group] [MulAction group points]
    (first second : points) := {element : group // element • first = second}

@[expose] def transporterEquivStabilizer {group points : Type*} [Group group] [MulAction group points]
    (first second : points) (mover : group) (moves : mover • first = second) :
    Transporters (group := group) first second ≃ MulAction.stabilizer group first where
  toFun transporter := ⟨mover⁻¹ * transporter.val, by
    apply MulAction.mem_stabilizer_iff.mpr
    rw [mul_smul, transporter.property, ← moves, inv_smul_smul]⟩
  invFun stabilizer := ⟨mover * stabilizer.val, by
    rw [mul_smul, MulAction.mem_stabilizer_iff.mp stabilizer.property, moves]⟩
  left_inv transporter := by
    apply Subtype.ext
    simp only [mul_inv_cancel_left]
  right_inv stabilizer := by
    apply Subtype.ext
    simp only [inv_mul_cancel_left]

theorem transporter_card_dvd {group points : Type*} [Group group] [MulAction group points]
    (first second : points) (same_orbit : ∃ mover : group, mover • first = second) :
    Nat.card (Transporters (group := group) first second) ∣ Nat.card group := by
  obtain ⟨mover, moves⟩ := same_orbit
  rw [Nat.card_congr (transporterEquivStabilizer first second mover moves)]
  exact (MulAction.stabilizer group first).card_subgroup_dvd_card

theorem automorphism_conjugate_map {group : Type*} [Group group]
    (automorphism : MulAut group) (subgroup : Subgroup group) (element : group) :
    (subgroup.map (MulAut.conj element).toMonoidHom).map automorphism.toMonoidHom =
      (subgroup.map automorphism.toMonoidHom).map
        (MulAut.conj (automorphism element)).toMonoidHom := by
  have intertwines : automorphism.toMonoidHom.comp (MulAut.conj element).toMonoidHom =
      (MulAut.conj (automorphism element)).toMonoidHom.comp automorphism.toMonoidHom := by
    ext original
    change automorphism (element * original * element⁻¹) =
      automorphism element * automorphism original * (automorphism element)⁻¹
    rw [map_mul, map_mul, map_inv]
  rw [Subgroup.map_map, Subgroup.map_map, intertwines]

@[expose, instance_reducible] def conjugatorAction {actor group : Type*} [Group actor] [Group group]
    (homomorphism : actor →* MulAut group) (first second : Subgroup group)
    (first_invariant : ∀ element : actor, first.map (homomorphism element).toMonoidHom = first)
    (second_invariant : ∀ element : actor, second.map (homomorphism element).toMonoidHom = second) :
    MulAction actor (Transporters (group := group) first second) where
  smul acting transporter := ⟨homomorphism acting transporter.val, by
    have conjugates : first.map (MulAut.conj transporter.val).toMonoidHom = second :=
      transporter.property
    have mapped := congrArg (fun subgroup : Subgroup group =>
      subgroup.map (homomorphism acting).toMonoidHom) conjugates
    rw [automorphism_conjugate_map, first_invariant, second_invariant] at mapped
    exact mapped⟩
  one_smul transporter := by
    apply Subtype.ext
    change homomorphism 1 transporter.val = transporter.val
    rw [map_one]
    rfl
  mul_smul first_actor second_actor transporter := by
    apply Subtype.ext
    change homomorphism (first_actor * second_actor) transporter.val =
      homomorphism first_actor (homomorphism second_actor transporter.val)
    rw [map_mul]
    rfl

theorem exists_fixed_conjugator_of_coprime {actor group : Type*} [Group actor] [Group group]
    [Finite group] (prime : ℕ) [Fact (Nat.Prime prime)] (prime_actor : IsPGroup prime actor)
    (coprime : ¬ prime ∣ Nat.card group) (homomorphism : actor →* MulAut group)
    (first second : Subgroup group)
    (first_invariant : ∀ element : actor, first.map (homomorphism element).toMonoidHom = first)
    (second_invariant : ∀ element : actor, second.map (homomorphism element).toMonoidHom = second)
    (conjugates : ∃ element : group, first.map (MulAut.conj element).toMonoidHom = second) :
    ∃ element : group, first.map (MulAut.conj element).toMonoidHom = second ∧
      ∀ acting : actor, homomorphism acting element = element := by
  let := conjugatorAction homomorphism first second first_invariant second_invariant
  have not_divides : ¬ prime ∣ Nat.card (Transporters (group := group) first second) := by
    intro divides
    exact coprime (divides.trans (transporter_card_dvd first second conjugates))
  obtain ⟨transporter, fixed⟩ := prime_actor.nonempty_fixed_point_of_prime_not_dvd_card
    (Transporters (group := group) first second) not_divides
  refine ⟨transporter.val, transporter.property, ?_⟩
  intro acting
  exact congrArg Subtype.val (MulAction.mem_fixedPoints.mp fixed acting)

theorem invariant_sylows_conjugate_of_coprime {actor group : Type*}
    [Group actor] [Group group] [Finite group]
    (acting_prime sylow_prime : ℕ) [Fact (Nat.Prime acting_prime)]
    [Fact (Nat.Prime sylow_prime)] (prime_actor : IsPGroup acting_prime actor)
    (coprime : ¬ acting_prime ∣ Nat.card group) (homomorphism : actor →* MulAut group)
    (first second : Sylow sylow_prime group)
    (first_invariant : ∀ element : actor,
      (first : Subgroup group).map (homomorphism element).toMonoidHom = first)
    (second_invariant : ∀ element : actor,
      (second : Subgroup group).map (homomorphism element).toMonoidHom = second) :
    ∃ element : group, (first : Subgroup group).map (MulAut.conj element).toMonoidHom = second ∧
      ∀ acting : actor, homomorphism acting element = element := by
  apply exists_fixed_conjugator_of_coprime acting_prime prime_actor coprime homomorphism
    first second first_invariant second_invariant
  obtain ⟨element, conjugates⟩ := MulAction.exists_smul_eq group first second
  refine ⟨element, ?_⟩
  rw [← CFSG.OrderReductions.FixedPairSylow.sylow_smul_subgroup_eq, conjugates]

end CFSG.OrderReductions.FixedConjugator
