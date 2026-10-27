module

public import CFSG.Open.OrderForm

public section

open CFSG.Open
open Finset

namespace CFSG.OrderReductions.LinearOrders

@[expose] noncomputable def specialLinearEquivDetKernel (field : Type*) [Field field]
    (degree : ℕ) :
    Matrix.SpecialLinearGroup (Fin degree) field ≃*
      (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin degree) field →*
        fieldˣ).ker := by
  let inclusion := Matrix.SpecialLinearGroup.toGL.codRestrict
    (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin degree) field →*
      fieldˣ).ker (by
        intro matrix
        exact Matrix.SpecialLinearGroup.coeToGL_det matrix)
  apply MulEquiv.ofBijective inclusion
  constructor
  · intro first second equal_images
    exact Matrix.SpecialLinearGroup.toGL_injective (congrArg Subtype.val equal_images)
  · intro matrix
    have in_range : matrix.val ∈ Set.range
        (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin degree) field →*
          Matrix.GeneralLinearGroup (Fin degree) field) := by
      change matrix.val ∈ Matrix.SpecialLinearGroup.toGL.range
      rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
      exact matrix.property
    obtain ⟨preimage, preimage_eq⟩ := in_range
    exact ⟨preimage, Subtype.ext preimage_eq⟩

theorem card_generalLinear_eq_units_mul_specialLinear (field : Type*) [Field field]
    (degree : ℕ) (positive_degree : 0 < degree) :
    Nat.card (Matrix.GeneralLinearGroup (Fin degree) field) =
      Nat.card fieldˣ * Nat.card (Matrix.SpecialLinearGroup (Fin degree) field) := by
  have : Nonempty (Fin degree) := ⟨⟨0, positive_degree⟩⟩
  let determinant := (Matrix.GeneralLinearGroup.det :
    Matrix.GeneralLinearGroup (Fin degree) field →* fieldˣ)
  have quotient_card : Nat.card
      (Matrix.GeneralLinearGroup (Fin degree) field ⧸ determinant.ker) = Nat.card fieldˣ :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective determinant
      Matrix.GeneralLinearGroup.det_surjective).toEquiv
  have kernel_card : Nat.card determinant.ker =
      Nat.card (Matrix.SpecialLinearGroup (Fin degree) field) :=
    (Nat.card_congr (specialLinearEquivDetKernel field degree).toEquiv).symm
  rw [determinant.ker.card_eq_card_quotient_mul_card_subgroup, quotient_card, kernel_card]

theorem card_rootsOfUnity_finite_field (field : Type*) [Field field] [Finite field]
    (degree : ℕ) : Nat.card (rootsOfUnity degree field) = degree.gcd (Nat.card field - 1) := by
  rw [rootsOfUnity_eq_ker, IsCyclic.card_powMonoidHom_ker, Nat.card_units, Nat.gcd_comm]

theorem card_specialLinear_center (field : Type*) [Field field] [Finite field]
    (degree : ℕ) (positive_degree : 0 < degree) :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin degree) field)) =
      degree.gcd (Nat.card field - 1) := by
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity'
    (R := field) (⟨0, positive_degree⟩ : Fin degree)).toEquiv]
  simpa using card_rootsOfUnity_finite_field field degree

theorem prod_positive_powers (order degree : ℕ) :
    (∏ index ∈ range degree, (order ^ (index + 1) - 1)) =
      ∏ index ∈ Icc 1 degree, (order ^ index - 1) := by
  induction degree with
  | zero => simp
  | succ degree induction_hypothesis =>
      rw [prod_range_succ, prod_Icc_succ_top (by omega), induction_hypothesis]

theorem generalLinear_order_product (order degree : ℕ) :
    (∏ index ∈ range degree, (order ^ degree - order ^ index)) =
      order ^ (degree * (degree - 1) / 2) *
        ∏ index ∈ Icc 1 degree, (order ^ index - 1) := by
  have factorization : (∏ index ∈ range degree, (order ^ degree - order ^ index)) =
      ∏ index ∈ range degree, order ^ index * (order ^ (degree - index) - 1) := by
    apply prod_congr rfl
    intro index in_range
    have index_bound : index ≤ degree := Nat.le_of_lt (mem_range.mp in_range)
    rw [Nat.mul_sub, ← pow_add, Nat.add_sub_of_le index_bound, mul_one]
  have reverse_factors : (∏ index ∈ range degree, (order ^ (degree - index) - 1)) =
      ∏ index ∈ range degree, (order ^ (index + 1) - 1) := by
    calc
      _ = ∏ index ∈ range degree, (order ^ ((degree - 1 - index) + 1) - 1) := by
        apply prod_congr rfl
        intro index in_range
        have index_bound := mem_range.mp in_range
        congr 2
        omega
      _ = _ := prod_range_reflect (fun index => order ^ (index + 1) - 1) degree
  rw [factorization, prod_mul_distrib, prod_pow_eq_pow_sum, sum_range_id,
    reverse_factors, prod_positive_powers]

theorem card_generalLinear (field : Type*) [Field field] [Finite field] (degree : ℕ) :
    Nat.card (Matrix.GeneralLinearGroup (Fin degree) field) =
      Nat.card field ^ (degree * (degree - 1) / 2) *
        ∏ index ∈ Icc 1 degree, (Nat.card field ^ index - 1) := by
  let := Fintype.ofFinite field
  rw [Matrix.card_GL_field, Fin.prod_univ_eq_prod_range
    (fun index => Fintype.card field ^ degree - Fintype.card field ^ index) degree]
  simpa only [Nat.card_eq_fintype_card] using
    generalLinear_order_product (Fintype.card field) degree

theorem prod_positive_powers_split (order degree : ℕ) (positive_degree : 0 < degree) :
    (∏ index ∈ Icc 1 degree, (order ^ index - 1)) =
      (order - 1) * ∏ index ∈ Icc 2 degree, (order ^ index - 1) := by
  obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive_degree)
  induction remaining with
  | zero => simp
  | succ remaining induction_hypothesis =>
      rw [prod_Icc_succ_top (a := 1) (b := remaining + 1) (by omega),
        prod_Icc_succ_top (a := 2) (b := remaining + 1) (by omega),
        induction_hypothesis (by omega), mul_assoc]

theorem card_specialLinear (field : Type*) [Field field] [Finite field]
    (degree : ℕ) (positive_degree : 0 < degree) :
    Nat.card (Matrix.SpecialLinearGroup (Fin degree) field) =
      Nat.card field ^ (degree * (degree - 1) / 2) *
        ∏ index ∈ Icc 2 degree, (Nat.card field ^ index - 1) := by
  have positive_units : 0 < Nat.card field - 1 := by
    have := Nat.card_pos (α := fieldˣ)
    rwa [Nat.card_units] at this
  apply Nat.mul_left_cancel positive_units
  rw [← Nat.card_units field, ← card_generalLinear_eq_units_mul_specialLinear field degree
    positive_degree, card_generalLinear, Nat.card_units,
    prod_positive_powers_split _ _ positive_degree]
  ac_rfl

theorem card_projectiveSpecialLinear (field : Type*) [Field field] [Finite field]
    (degree : ℕ) (positive_degree : 0 < degree) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin degree) field) =
      (Nat.card field ^ (degree * (degree - 1) / 2) *
        ∏ index ∈ Icc 2 degree, (Nat.card field ^ index - 1)) /
          degree.gcd (Nat.card field - 1) := by
  have quotient_order := (Subgroup.center
    (Matrix.SpecialLinearGroup (Fin degree) field)).card_eq_card_quotient_mul_card_subgroup
  have positive_center : 0 < Nat.card (Subgroup.center
      (Matrix.SpecialLinearGroup (Fin degree) field)) := Nat.card_pos
  change Nat.card (Matrix.SpecialLinearGroup (Fin degree) field ⧸
    Subgroup.center (Matrix.SpecialLinearGroup (Fin degree) field)) = _
  rw [← card_specialLinear field degree positive_degree,
    ← card_specialLinear_center field degree positive_degree, quotient_order,
    Nat.mul_div_cancel _ positive_center]

theorem card_projectiveSpecialLinear_eq_orderA (field : Type*) [Field field] [Finite field]
    (rank : ℕ) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin (rank + 1)) field) =
      orderA rank (Nat.card field) := by
  rw [card_projectiveSpecialLinear field (rank + 1) (by omega)]
  simp only [orderA, Nat.add_sub_cancel, Nat.mul_comm]

theorem card_projectiveSpecialLinear_mem_orders (field : Type*) [Field field] [Finite field]
    (rank : ℕ) (positive_rank : 1 ≤ rank) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin (rank + 1)) field) ∈ cfsgOrders := by
  let := Fintype.ofFinite field
  have prime_power : IsPrimePow (Nat.card field) := by
    simpa only [Nat.card_eq_fintype_card] using FiniteField.isPrimePow_card field
  simp only [cfsgOrders, Set.mem_union, Set.mem_ofPred_eq]
  iterate 9 apply Or.inl
  exact Or.inr ⟨rank, Nat.card field, positive_rank, prime_power,
    card_projectiveSpecialLinear_eq_orderA field rank⟩

end CFSG.OrderReductions.LinearOrders
