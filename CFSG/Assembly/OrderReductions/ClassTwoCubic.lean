module

public import Mathlib
public import CFSG.Mathlib.GroupTheory.Basic
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
public import CFSG.Assembly.OrderReductions.AlternatingPairing
public import CFSG.Assembly.OrderReductions.ClassTwoPairing

public section

namespace CFSG.OrderReductions.ClassTwoCubic

open CFSG.OrderReductions.ClassTwoPairing

attribute [local instance] commutatorElement centerCommGroup

theorem eq_one_of_square_eq_one_of_odd {group : Type*} [Group group]
    (odd_order : Odd (Nat.card group)) (element : group) (square : element ^ 2 = 1) :
    element = 1 := by
  rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one square) with
    order_one | order_two
  · exact orderOf_eq_one_iff.mp order_one
  · have odd_element := odd_order.of_dvd_nat (orderOf_dvd_natCard element)
    rw [order_two] at odd_element
    exact False.elim ((by decide : ¬ Odd (2 : ℕ)) odd_element)

@[expose] def difference {group : Type*} [Group group] (automorphism : MulAut group) (element : group) : group :=
  element⁻¹ * automorphism element

theorem difference_abelianization {group : Type*} [Group group]
    (automorphism : MulAut group) (element : group) :
    Additive.ofMul (Abelianization.of (difference automorphism element)) =
      (abelianizationAutomorphism automorphism).toAdditive (Additive.ofMul (Abelianization.of element)) -
        Additive.ofMul (Abelianization.of element) := by
  rw [sub_eq_add_neg]
  change Abelianization.of (element⁻¹ * automorphism element) =
    Abelianization.map automorphism.toMonoidHom (Abelianization.of element) * (Abelianization.of element)⁻¹
  rw [map_mul, map_inv, Abelianization.map_of, mul_comm]
  rfl

theorem abelianizationAutomorphism_commutes {group : Type*} [Group group]
    (first second : MulAut group)
    (commutes : ∀ element : group, first (second element) = second (first element))
    (element : Additive (Abelianization group)) :
    (abelianizationAutomorphism first).toAdditive ((abelianizationAutomorphism second).toAdditive element) =
      (abelianizationAutomorphism second).toAdditive ((abelianizationAutomorphism first).toAdditive element) := by
  obtain ⟨original, equal⟩ := abelianization_surjective (Additive.toMul element)
  change Abelianization.map first.toMonoidHom (Abelianization.map second.toMonoidHom (Additive.toMul element)) =
    Abelianization.map second.toMonoidHom (Abelianization.map first.toMonoidHom (Additive.toMul element))
  rw [← equal, Abelianization.map_of, Abelianization.map_of, Abelianization.map_of,
    Abelianization.map_of]
  exact congrArg Abelianization.of (commutes original)

theorem differences_commute {group : Type*} [Group group]
    (central : commutator group ≤ Subgroup.center group) (odd_order : Odd (Nat.card group))
    (first second : MulAut group)
    (commutes : ∀ element : group, first (second element) = second (first element))
    (first_fixed_commutator : ∀ element : group, element ∈ commutator group → first element = element)
    (second_fixed_commutator : ∀ element : group, element ∈ commutator group → second element = element)
    (element : group)
    (first_fixed : first (difference first (difference second element)) = difference first (difference second element))
    (second_fixed : second (difference first (difference second element)) = difference first (difference second element)) :
    Commute (difference first element) (difference second element) := by
  have no_two_torsion : ∀ value : Additive (Subgroup.center group), value + value = 0 → value = 0 := by
    intro value equal
    change (Additive.toMul value : Subgroup.center group) = 1
    apply Subtype.ext
    apply eq_one_of_square_eq_one_of_odd odd_order
    change (Additive.toMul value : Subgroup.center group) * Additive.toMul value = 1 at equal
    simpa only [pow_two, Subgroup.coe_mul, Subgroup.coe_one] using
      congrArg (fun entry : Subgroup.center group => entry.val) equal
  let quotient_element := Additive.ofMul (Abelianization.of element)
  let double_element := Additive.ofMul (Abelianization.of (difference first (difference second element)))
  have double_eq : double_element =
      (abelianizationAutomorphism first).toAdditive
          ((abelianizationAutomorphism second).toAdditive quotient_element - quotient_element) -
        ((abelianizationAutomorphism second).toAdditive quotient_element - quotient_element) := by
    dsimp [double_element, quotient_element]
    rw [difference_abelianization, difference_abelianization]
  have first_quotient_fixed : (abelianizationAutomorphism first).toAdditive double_element = double_element := by
    change Abelianization.map first.toMonoidHom (Abelianization.of _) = Abelianization.of _
    rw [Abelianization.map_of]
    exact congrArg Abelianization.of first_fixed
  have second_quotient_fixed : (abelianizationAutomorphism second).toAdditive double_element = double_element := by
    change Abelianization.map second.toMonoidHom (Abelianization.of _) = Abelianization.of _
    rw [Abelianization.map_of]
    exact congrArg Abelianization.of second_fixed
  rw [double_eq] at first_quotient_fixed second_quotient_fixed
  have vanishing := CFSG.OrderReductions.AlternatingPairing.invariant_quadratic_vanishing
    (additiveCommutatorPairing central) (additiveCommutatorPairing_alternating central)
    no_two_torsion (abelianizationAutomorphism first).toAdditive
    (abelianizationAutomorphism second).toAdditive (abelianizationAutomorphism_commutes first second commutes)
    (additiveCommutatorPairing_invariant central first first_fixed_commutator)
    (additiveCommutatorPairing_invariant central second second_fixed_commutator)
    quotient_element first_quotient_fixed second_quotient_fixed
  dsimp [quotient_element] at vanishing
  rw [← difference_abelianization, ← difference_abelianization] at vanishing
  change commutatorPairing central (Abelianization.of (difference first element))
    (Abelianization.of (difference second element)) = 1 at vanishing
  rw [commutatorPairing_of] at vanishing
  apply commutatorElement_eq_one_iff_commute.mp
  exact congrArg (fun value : Subgroup.center group => value.val) vanishing

theorem cubic_trivial_differences_abelian {actors group : Type*} [CommGroup actors] [Group group]
    (action : actors →* MulAut group)
    (central : commutator group ≤ Subgroup.center group) (odd_order : Odd (Nat.card group))
    (fixed_commutator : ∀ actor : actors, ∀ element : group, element ∈ commutator group → action actor element = element)
    (element : group)
    (cubic : ∀ first second third : actors,
      difference (action third) (difference (action second) (difference (action first) element)) = 1) :
    IsMulCommutative ↥(Subgroup.closure (Set.range fun actor : actors => difference (action actor) element)) := by
  apply CFSG.subgroup_isMulCommutative_closure
  rintro left ⟨first, rfl⟩ right ⟨second, rfl⟩
  apply Commute.eq
  apply differences_commute central odd_order (action first) (action second)
  · intro value
    change (action first * action second) value = (action second * action first) value
    rw [← map_mul, ← map_mul, mul_comm]
  · exact fixed_commutator first
  · exact fixed_commutator second
  · have fixed := cubic second first first
    change (difference (action first) (difference (action second) element))⁻¹ *
      action first (difference (action first) (difference (action second) element)) = 1 at fixed
    exact (inv_mul_eq_one.mp fixed).symm
  · have fixed := cubic second first second
    change (difference (action first) (difference (action second) element))⁻¹ *
      action second (difference (action first) (difference (action second) element)) = 1 at fixed
    exact (inv_mul_eq_one.mp fixed).symm

end CFSG.OrderReductions.ClassTwoCubic
