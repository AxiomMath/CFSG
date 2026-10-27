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
public import CFSG.Assembly.OrderReductions.Helpers
public import CFSG.Assembly.OrderReductions.InvolutionGraph

public section

namespace CFSG.OrderReductions.UniqueInvolutionAction

open CFSG.OrderReductions.InvolutionGraph

theorem distinct_stabilizers_odd_intersection {group points : Type*} [Group group]
    [Finite group] [MulAction group points]
    (unique_fixed : ∀ involution : Involution group,
      ∀ first second : points, involution.val • first = first →
        involution.val • second = second → first = second)
    (first second : points) (distinct : first ≠ second) :
    Odd (Nat.card ↥(MulAction.stabilizer group first ⊓ MulAction.stabilizer group second)) := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  by_contra not_odd
  obtain ⟨element, element_order⟩ := exists_prime_orderOf_dvd_card' 2
    (Nat.not_odd_iff_even.mp not_odd).two_dvd
  let involution : Involution group :=
    ⟨element.val, by rw [Subgroup.orderOf_coe]; exact element_order⟩
  exact distinct (unique_fixed involution first second element.property.1 element.property.2)

theorem stabilizer_even_of_transitive {group points : Type*} [Group group] [Finite group]
    [MulAction group points] [MulAction.IsPretransitive group points]
    (even_order : Even (Nat.card group))
    (exists_fixed : ∀ involution : Involution group, ∃ point : points,
      involution.val • point = point) (point : points) :
    Even (Nat.card (MulAction.stabilizer group point)) := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨element, element_order⟩ := exists_prime_orderOf_dvd_card' 2 even_order.two_dvd
  let involution : Involution group := ⟨element, element_order⟩
  obtain ⟨fixed_point, fixes⟩ := exists_fixed involution
  obtain ⟨conjugator, moves⟩ := MulAction.exists_smul_eq group fixed_point point
  have conjugated_fixed : (conjugator • involution).val • point = point := by
    rw [involution_smul_val, ← moves, mul_smul, mul_smul, inv_smul_smul, fixes]
  apply even_iff_two_dvd.mpr
  rw [← (conjugator • involution).property]
  exact Subgroup.orderOf_dvd_natCard _ conjugated_fixed

theorem stabilizer_ne_top_of_transitive {group points : Type*} [Group group]
    [MulAction group points] [MulAction.IsPretransitive group points] [Nontrivial points]
    (point : points) : MulAction.stabilizer group point ≠ ⊤ := by
  obtain ⟨other, distinct⟩ := exists_ne point
  obtain ⟨element, moves⟩ := MulAction.exists_smul_eq group point other
  intro equal_top
  have fixed : element • point = point := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [equal_top]
    trivial
  exact distinct (moves.symm.trans fixed)

theorem stronglyEmbedded_stabilizer_of_unique_fixed {group points : Type*} [Group group]
    [Finite group] [MulAction group points] [MulAction.IsPretransitive group points]
    [Nontrivial points] (even_order : Even (Nat.card group))
    (unique_fixed : ∀ involution : Involution group, ∃! point : points,
      involution.val • point = point) (point : points) :
    StronglyEmbedded (MulAction.stabilizer group point) := by
  have at_most_one : ∀ involution : Involution group,
      ∀ first second : points, involution.val • first = first →
        involution.val • second = second → first = second := by
    intro involution first second first_fixed second_fixed
    obtain ⟨fixed_point, _, unique⟩ := unique_fixed involution
    exact (unique first first_fixed).trans (unique second second_fixed).symm
  refine ⟨stabilizer_ne_top_of_transitive point,
    stabilizer_even_of_transitive even_order
      (fun involution => (unique_fixed involution).exists) point, ?_⟩
  intro conjugator not_mem
  rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  apply distinct_stabilizers_odd_intersection at_most_one point (conjugator • point)
  intro equal_points
  exact not_mem equal_points.symm

theorem perfect_unique_involution_action_card_mod_four {group points : Type*} [Group group]
    [Group.IsPerfect group] [Finite points] [MulAction group points]
    (involution : Involution group)
    (unique_fixed : ∃! point : points, involution.val • point = point) :
    Nat.card points % 4 = 1 := by
  classical
  let _ : Fintype points := Fintype.ofFinite points
  let permutation := MulAction.toPermHom group points involution.val
  have permutation_square : permutation ^ 2 = 1 := by
    change (MulAction.toPermHom group points involution.val) ^ 2 = 1
    rw [← map_pow]
    have square_one := pow_orderOf_eq_one involution.val
    rw [involution.property] at square_one
    rw [square_one, map_one]
  have fixed_card : Fintype.card (Function.fixedPoints permutation) = 1 := by
    obtain ⟨point, fixed, unique⟩ := unique_fixed
    have : Nonempty (Function.fixedPoints permutation) := ⟨⟨point, fixed⟩⟩
    have : Subsingleton (Function.fixedPoints permutation) := by
      constructor
      intro first second
      apply Subtype.ext
      exact (unique first.val first.property).trans (unique second.val second.property).symm
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_unique
  have sign_one : Equiv.Perm.sign permutation = 1 := by
    have trivial_sign := CFSG.OrderReductions.Helpers.perfect_hom_to_commutative_eq_one group ℤˣ
      (Equiv.Perm.sign.comp (MulAction.toPermHom group points))
    exact congrArg (fun homomorphism : group →* ℤˣ => homomorphism involution.val) trivial_sign
  have sign_formula := Equiv.Perm.sign_of_pow_two_eq_one permutation_square
  rw [fixed_card, sign_one] at sign_formula
  have even_half : Even ((Fintype.card points - 1) / 2) :=
    (neg_one_pow_eq_one_iff_even (R := ℤˣ) (by decide)).mp sign_formula.symm
  have two_divides : 2 ∣ Fintype.card points - 1 := by
    have support_divides := Equiv.Perm.two_dvd_card_support permutation_square
    have support_card : permutation.support.card = Fintype.card points - 1 := by
      have support_complement : (permutation.support : Set points) =
          (Function.fixedPoints permutation)ᶜ := by
        ext point
        exact Equiv.Perm.mem_support
      rw [← Set.ncard_coe_finset, support_complement, Set.ncard_compl,
        ← Set.ncard_coe, Set.ncard_univ]
      simp only [Nat.card_eq_fintype_card, fixed_card]
    rwa [support_card] at support_divides
  have positive : 0 < Fintype.card points := by
    obtain ⟨point, _⟩ := unique_fixed.exists
    exact Fintype.card_pos_iff.mpr ⟨point⟩
  rw [Nat.card_eq_fintype_card]
  obtain ⟨half, half_eq⟩ := even_half
  omega

end CFSG.OrderReductions.UniqueInvolutionAction
