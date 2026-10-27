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
public import CFSG.Assembly.OrderReductions.InvertedSubgroup

public section

namespace CFSG.OrderReductions.AlternatingPairing

theorem antisymmetric {domain target : Type*} [AddCommGroup domain] [AddCommGroup target]
    (pairing : domain →+ domain →+ target) (alternating : ∀ element : domain, pairing element element = 0)
    (first second : domain) : pairing first second = -pairing second first := by
  have sum_zero := alternating (first + second)
  simp only [map_add, AddMonoidHom.add_apply, alternating, zero_add, add_zero] at sum_zero
  rw [add_comm] at sum_zero
  exact eq_neg_of_add_eq_zero_left sum_zero

theorem invariant_quadratic_vanishing {domain target : Type*} [AddCommGroup domain] [AddCommGroup target]
    (pairing : domain →+ domain →+ target) (alternating : ∀ element : domain, pairing element element = 0)
    (no_two_torsion : ∀ element : target, element + element = 0 → element = 0)
    (first second : domain ≃+ domain)
    (commutes : ∀ element : domain, first (second element) = second (first element))
    (first_invariant : ∀ left right : domain, pairing (first left) (first right) = pairing left right)
    (second_invariant : ∀ left right : domain, pairing (second left) (second right) = pairing left right)
    (element : domain)
    (first_fixed : first (first (second element - element) - (second element - element)) =
      first (second element - element) - (second element - element))
    (second_fixed : second (first (second element - element) - (second element - element)) =
      first (second element - element) - (second element - element)) :
    pairing (first element - element) (second element - element) = 0 := by
  let first_difference := first element - element
  let second_difference := second element - element
  let double_difference := first second_difference - second_difference
  have first_element : first element = element + first_difference := by
    dsimp [first_difference]
    abel
  have second_element : second element = element + second_difference := by
    dsimp [second_difference]
    abel
  have first_second : first second_difference = second_difference + double_difference := by
    dsimp [double_difference]
    abel
  have second_first : second first_difference = first_difference + double_difference := by
    dsimp [first_difference, second_difference, double_difference]
    simp only [map_sub]
    rw [commutes]
    abel
  have first_double : first double_difference = double_difference := first_fixed
  have second_double : second double_difference = double_difference := second_fixed
  have first_orthogonal : pairing first_difference double_difference = 0 := by
    have invariant := first_invariant element double_difference
    rw [first_element, first_double, map_add, AddMonoidHom.add_apply] at invariant
    exact add_left_cancel (invariant.trans (add_zero _).symm)
  have second_orthogonal : pairing second_difference double_difference = 0 := by
    have invariant := second_invariant element double_difference
    rw [second_element, second_double, map_add, AddMonoidHom.add_apply] at invariant
    exact add_left_cancel (invariant.trans (add_zero _).symm)
  have first_equation : pairing element double_difference + pairing first_difference second_difference = 0 := by
    have invariant := first_invariant element second_difference
    rw [first_element, first_second] at invariant
    simp only [map_add, AddMonoidHom.add_apply, first_orthogonal, add_zero] at invariant
    apply add_left_cancel (a := pairing element second_difference)
    calc
      pairing element second_difference +
          (pairing element double_difference + pairing first_difference second_difference) =
        pairing element second_difference + pairing element double_difference +
          pairing first_difference second_difference := (add_assoc _ _ _).symm
      _ = pairing element second_difference + pairing first_difference second_difference +
          pairing element double_difference := by abel
      _ = pairing element second_difference := invariant
      _ = pairing element second_difference + 0 := (add_zero _).symm
  have second_equation : pairing element double_difference + pairing second_difference first_difference = 0 := by
    have invariant := second_invariant element first_difference
    rw [second_element, second_first] at invariant
    simp only [map_add, AddMonoidHom.add_apply, second_orthogonal, add_zero] at invariant
    apply add_left_cancel (a := pairing element first_difference)
    calc
      pairing element first_difference +
          (pairing element double_difference + pairing second_difference first_difference) =
        pairing element first_difference + pairing element double_difference +
          pairing second_difference first_difference := (add_assoc _ _ _).symm
      _ = pairing element first_difference + pairing second_difference first_difference +
          pairing element double_difference := by abel
      _ = pairing element first_difference := invariant
      _ = pairing element first_difference + 0 := (add_zero _).symm
  have symmetric : pairing first_difference second_difference = pairing second_difference first_difference :=
    add_left_cancel (first_equation.trans second_equation.symm)
  apply no_two_torsion
  calc
    pairing first_difference second_difference + pairing first_difference second_difference =
      pairing first_difference second_difference + pairing second_difference first_difference := congrArg _ symmetric
    _ = 0 := by rw [antisymmetric pairing alternating second_difference first_difference, add_neg_cancel]

end CFSG.OrderReductions.AlternatingPairing
