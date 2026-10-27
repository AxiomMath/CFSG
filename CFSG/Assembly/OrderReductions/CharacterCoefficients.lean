module

public import CFSG.Assembly.OrderReductions.NormThreeCoefficients
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.OrderReductions.CharacterCoefficients

@[expose] noncomputable def scalarProduct {field group : Type*} [Field field] [Group group] [Fintype group]
    (first second : group → field) : field :=
  (Nat.card group : field)⁻¹ * ∑ element : group, first element * second element⁻¹

theorem scalarProduct_sum_left {field group index : Type*} [Field field] [Group group] [Fintype group]
    (indices : Finset index) (functions : index → group → field) (function : group → field) :
    scalarProduct (fun element => ∑ current ∈ indices, functions current element) function =
      ∑ current ∈ indices, scalarProduct (functions current) function := by
  simp only [scalarProduct, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]

theorem scalarProduct_sum_right {field group index : Type*} [Field field] [Group group] [Fintype group]
    (indices : Finset index) (functions : index → group → field) (function : group → field) :
    scalarProduct function (fun element => ∑ current ∈ indices, functions current element) =
      ∑ current ∈ indices, scalarProduct function (functions current) := by
  simp only [scalarProduct, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem scalarProduct_mul_left {field group : Type*} [Field field] [Group group] [Fintype group]
    (coefficient : field) (first second : group → field) :
    scalarProduct (fun element => coefficient * first element) second =
      coefficient * scalarProduct first second := by
  simp only [scalarProduct, mul_assoc, ← Finset.mul_sum]
  ring

theorem scalarProduct_mul_right {field group : Type*} [Field field] [Group group] [Fintype group]
    (coefficient : field) (first second : group → field) :
    scalarProduct first (fun element => coefficient * second element) =
      coefficient * scalarProduct first second := by
  have commute : ∀ element : group,
      first element * (coefficient * second element⁻¹) = coefficient * (first element * second element⁻¹) :=
    fun _ => by ring
  simp only [scalarProduct, commute, ← Finset.mul_sum]
  ring

@[expose] def virtualCombination {field group index : Type*} [Field field] [Group group]
    (functions : index → group → field) (coefficients : index →₀ ℤ) (element : group) : field :=
  ∑ current ∈ coefficients.support, (coefficients current : field) * functions current element

theorem scalarProduct_combination_right {field group index : Type*} [Field field] [Group group]
    [Fintype group] [DecidableEq index] (functions : index → group → field)
    (orthonormal : ∀ first second,
      scalarProduct (functions first) (functions second) = if first = second then 1 else 0)
    (coefficients : index →₀ ℤ) (current : index) :
    scalarProduct (virtualCombination functions coefficients) (functions current) =
      (coefficients current : field) := by
  change scalarProduct (fun element => ∑ other ∈ coefficients.support,
    (coefficients other : field) * functions other element) (functions current) = _
  rw [scalarProduct_sum_left]
  simp_rw [scalarProduct_mul_left, orthonormal]
  by_cases membership : current ∈ coefficients.support
  · rw [Finset.sum_eq_single current]
    · simp
    · intro other _ distinct
      simp [distinct]
    · exact fun outside => False.elim (outside membership)
  · have zero_coefficient : coefficients current = 0 := by
      simpa only [Finsupp.mem_support_iff, not_not] using membership
    rw [zero_coefficient, Int.cast_zero]
    apply Finset.sum_eq_zero
    intro other other_mem
    have distinct : other ≠ current := by rintro rfl; exact membership other_mem
    simp [distinct]

theorem scalarProduct_combination_self {field group index : Type*} [Field field] [Group group]
    [Fintype group] [DecidableEq index] (functions : index → group → field)
    (orthonormal : ∀ first second,
      scalarProduct (functions first) (functions second) = if first = second then 1 else 0)
    (coefficients : index →₀ ℤ) :
    scalarProduct (virtualCombination functions coefficients) (virtualCombination functions coefficients) =
      ((∑ current ∈ coefficients.support, coefficients current ^ 2 : ℤ) : field) := by
  change scalarProduct (virtualCombination functions coefficients)
    (fun element => ∑ current ∈ coefficients.support, (coefficients current : field) * functions current element) = _
  rw [scalarProduct_sum_right]
  simp_rw [scalarProduct_mul_right, scalarProduct_combination_right functions orthonormal]
  simp only [pow_two, Int.cast_sum, Int.cast_mul]

theorem characters_orthonormal {field group index : Type*} [Field field] [CharZero field]
    [IsAlgClosed field] [Group group] [Fintype group] [DecidableEq index]
    (vectors : index → Type*) [∀ current, AddCommGroup (vectors current)]
    [∀ current, Module field (vectors current)] [∀ current, FiniteDimensional field (vectors current)]
    (representations : ∀ current, Representation field group (vectors current))
    [∀ current, (representations current).IsIrreducible]
    (inequivalent : ∀ first second, first ≠ second → IsEmpty ((representations first).Equiv (representations second)))
    (first second : index) :
    scalarProduct (representations first).character (representations second).character =
      if first = second then 1 else 0 := by
  classical
  let := invertibleOfNonzero (Nat.cast_ne_zero.mpr (ne_of_gt Nat.card_pos) : (Nat.card group : field) ≠ 0)
  rw [scalarProduct, Representation.char_orthonormal]
  by_cases equal : first = second
  · subst second
    have self_equiv : Nonempty ((representations first).Equiv (representations first)) :=
      ⟨Representation.Equiv.refl _⟩
    simp only [self_equiv, ↓reduceIte]
  · have : IsEmpty ((representations second).Equiv (representations first)) :=
      inequivalent second first (Ne.symm equal)
    simp only [not_nonempty_iff.mpr inferInstance, equal, ↓reduceIte]

theorem norm_three_decomposition {field group index : Type*} [Field field] [CharZero field]
    [Group group] [Fintype group] [DecidableEq index]
    (functions : index → group → field)
    (orthonormal : ∀ first second,
      scalarProduct (functions first) (functions second) = if first = second then 1 else 0)
    (coefficients : index →₀ ℤ) (principal : index)
    (principal_trivial : ∀ element, functions principal element = 1)
    (principal_coefficient : scalarProduct (virtualCombination functions coefficients)
      (functions principal) = 1)
    (norm_three : scalarProduct (virtualCombination functions coefficients)
      (virtualCombination functions coefficients) = 3) :
    ∃ first second : index, first ≠ second ∧ first ≠ principal ∧ second ≠ principal ∧
      (coefficients first = 1 ∨ coefficients first = -1) ∧
      (coefficients second = 1 ∨ coefficients second = -1) ∧
      ∀ element, virtualCombination functions coefficients element =
        1 + (coefficients first : field) * functions first element +
          (coefficients second : field) * functions second element := by
  rw [scalarProduct_combination_right functions orthonormal] at principal_coefficient
  have principal_one : coefficients principal = 1 := by exact_mod_cast principal_coefficient
  rw [scalarProduct_combination_self functions orthonormal] at norm_three
  have integer_norm : (∑ current ∈ coefficients.support, coefficients current ^ 2) = 3 := by
    exact_mod_cast norm_three
  obtain ⟨first, second, distinct, first_distinct, second_distinct, first_sign, second_sign, support_eq⟩ :=
    CFSG.OrderReductions.NormThreeCoefficients.exists_two_signed_coefficients coefficients principal principal_one integer_norm
  refine ⟨first, second, distinct, first_distinct, second_distinct, first_sign, second_sign, ?_⟩
  intro element
  unfold virtualCombination
  rw [support_eq]
  simp [principal_one, principal_trivial, first_distinct, second_distinct, distinct, Ne.symm, add_assoc]

theorem irreducible_degree_ne_zero {field group vector : Type*} [Field field] [CharZero field]
    [Group group] [AddCommGroup vector] [Module field vector] [FiniteDimensional field vector]
    (representation : Representation field group vector) [representation.IsIrreducible] :
    representation.character 1 ≠ 0 := by
  have : Nontrivial representation.asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra field group) representation.asModule
  have : Nontrivial vector := representation.asModuleEquiv.injective.nontrivial
  rw [representation.char_one]
  exact Nat.cast_ne_zero.mpr (ne_of_gt (Module.finrank_pos (R := field) (M := vector)))

end CFSG.OrderReductions.CharacterCoefficients
