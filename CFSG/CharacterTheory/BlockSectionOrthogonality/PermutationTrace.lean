module

public import CFSG.CharacterTheory.BlockSectionOrthogonality.PermutationCycles
public import CFSG.CharacterTheory.BlockSectionOrthogonality.IdempotentTwist
public import CFSG.CharacterTheory.BlockSectionOrthogonality.LocalCoefficients

public section

open CFSG
namespace CFSG.BlockSectionOrthogonality.Helpers

attribute [local instance] Classical.propDecidable Classical.decEq

@[expose] noncomputable def permutationMatrix {index : Type*} [Fintype index]
    {ring : Type*} [Zero ring] [One ring] (permutation : Equiv.Perm index) :
    Matrix index index ring :=
  fun row column => if row = permutation column then 1 else 0

theorem matrix_mul_permutationMatrix {index : Type*} [Fintype index]
    {ring : Type*} [Semiring ring] (permutation : Equiv.Perm index)
    (matrix : Matrix index index ring) (row column : index) :
    (matrix * permutationMatrix (ring := ring) permutation) row column = matrix row (permutation column) := by
  classical
  simp [Matrix.mul_apply, permutationMatrix]

theorem permutationMatrix_mul_matrix {index : Type*} [Fintype index]
    {ring : Type*} [Semiring ring] (permutation : Equiv.Perm index)
    (matrix : Matrix index index ring) (row column : index) :
    (permutationMatrix (ring := ring) permutation * matrix) row column = matrix (permutation.symm row) column := by
  classical
  have hEquality : ∀ index, row = permutation index ↔ index = permutation.symm row := by
    intro index
    exact ⟨fun hEqual => by rw [hEqual, permutation.symm_apply_apply],
      fun hEqual => by rw [hEqual, permutation.apply_symm_apply]⟩
  simp [Matrix.mul_apply, permutationMatrix, hEquality]

noncomputable def diagonalTwist {index : Type*} [Fintype index] [DecidableEq index]
    {ring : Type*} [CommRing ring] (permutation : Equiv.Perm index) (root : ringˣ) :
    (Matrix index index ring)ˣ where
  val := Matrix.diagonal (fun index => ((root ^ cycleOffset permutation index : ringˣ) : ring))
  inv := Matrix.diagonal (fun index => (((root ^ cycleOffset permutation index)⁻¹ : ringˣ) : ring))
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    have hFunction : (fun index => (↑(root ^ cycleOffset permutation index) : ring) *
        ↑(root ^ cycleOffset permutation index)⁻¹) = fun _ => (1 : ring) := by
      funext index
      exact Units.mul_inv (root ^ cycleOffset permutation index)
    rw [hFunction, Matrix.diagonal_one]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    have hFunction : (fun index => (↑(root ^ cycleOffset permutation index)⁻¹ : ring) *
        ↑(root ^ cycleOffset permutation index)) = fun _ => (1 : ring) := by
      funext index
      exact Units.inv_mul (root ^ cycleOffset permutation index)
    rw [hFunction, Matrix.diagonal_one]

theorem diagonalTwist_permutationMatrix {index : Type*} [Fintype index] [DecidableEq index]
    {ring : Type*} [CommRing ring] (permutation : Equiv.Perm index)
    (prime : ℕ) (root : ringˣ) (hRoot : root ^ prime = 1)
    (hPeriods : ∀ index, prime ∣ Function.minimalPeriod permutation index) :
    (diagonalTwist permutation root : Matrix index index ring) * permutationMatrix permutation *
      (↑(diagonalTwist permutation root)⁻¹ : Matrix index index ring) =
        (root : ring) • permutationMatrix permutation := by
  ext row column
  change (Matrix.diagonal (fun index => ((root ^ cycleOffset permutation index : ringˣ) : ring)) *
    permutationMatrix (ring := ring) permutation * Matrix.diagonal
      (fun index => (((root ^ cycleOffset permutation index)⁻¹ : ringˣ) : ring))) row column = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  change _ = (root : ring) * permutationMatrix permutation row column
  by_cases hRow : row = permutation column
  · rw [hRow]
    simp only [permutationMatrix, ite_true, mul_one]
    have hColor := congrArg (fun unit : ringˣ => (unit : ring))
      (cycleRootColor_apply permutation prime root hRoot hPeriods column)
    rw [hColor, Units.val_mul, mul_assoc, Units.mul_inv, mul_one]
  · simp [permutationMatrix, hRow]

theorem diagonalTwist_residue {index : Type*} [Fintype index] [DecidableEq index]
    {ring : Type*} [CommRing ring] [IsLocalRing ring]
    (permutation : Equiv.Perm index) (root : ringˣ)
    (hRoot : IsLocalRing.residue ring (root : ring) = 1) :
    (IsLocalRing.residue ring).mapMatrix
      (diagonalTwist permutation root : Matrix index index ring) = 1 := by
  ext row column
  change IsLocalRing.residue ring (Matrix.diagonal _ row column) = _
  by_cases hRow : row = column
  · subst row
    simp [Matrix.diagonal, map_pow, hRoot]
  · simp [Matrix.diagonal, hRow]

theorem localPermutation_idempotent_trace_zero (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (prime : ℕ) (hPrime : prime.Prime) (hPrimeMem : (prime : BlocksAlgInt) ∈ m)
    {index : Type*} [Fintype index] (permutation primary : Equiv.Perm index)
    (hPrimary : BlocksIsPPart prime permutation primary) (hNoFixed : ∀ index, primary index ≠ index)
    (idempotent : Matrix index index (localCoefficientSubring m hm))
    (hIdempotent : idempotent * idempotent = idempotent)
    (hCommute : idempotent * permutationMatrix permutation = permutationMatrix permutation * idempotent) :
    (idempotent * permutationMatrix permutation).trace = 0 := by
  classical
  let complexRoot := Complex.exp (2 * ↑Real.pi * Complex.I / (prime : ℂ))
  have hPrimitive : IsPrimitiveRoot complexRoot prime :=
    Complex.isPrimitiveRoot_exp prime hPrime.ne_zero
  let root : localCoefficientSubring m hm :=
    ⟨complexRoot, integral_mem_localRing m hm (hPrimitive.isIntegral hPrime.pos)⟩
  have hRoot : root ^ prime = 1 := by
    apply Subtype.ext
    exact hPrimitive.pow_eq_one
  have hUnit := IsUnit.of_pow_eq_one hRoot hPrime.ne_zero
  let rootUnit := hUnit.unit
  have hRootUnitVal : (rootUnit : localCoefficientSubring m hm) = root := hUnit.unit_spec
  have hRootUnit : rootUnit ^ prime = 1 := by
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, hRootUnitVal, Units.val_one] using hRoot
  have hRootNeOne : root ≠ 1 := by
    intro hOne
    have hComplex := congrArg (fun value : localCoefficientSubring m hm => (value : ℂ)) hOne
    exact hPrimitive.ne_one hPrime.one_lt hComplex
  have hPeriods : ∀ index, prime ∣ Function.minimalPeriod permutation index := by
    intro index
    apply primaryPart_period_divisible permutation primary prime hPrime hPrimary hNoFixed
    rw [Equiv.Perm.coe_pow, Function.iterate_minimalPeriod]
  apply equivariant_idempotent_twist_trace_zero idempotent (permutationMatrix permutation)
    hIdempotent hCommute (diagonalTwist permutation rootUnit) (rootUnit : localCoefficientSubring m hm)
  · simpa only [hRootUnitVal] using hRootNeOne
  · exact diagonalTwist_permutationMatrix permutation prime rootUnit hRootUnit hPeriods
  · apply diagonalTwist_residue
    rw [hRootUnitVal]
    exact localCoefficient_root_residue_eq_one m hm prime hPrime hPrimeMem root hRoot

end CFSG.BlockSectionOrthogonality.Helpers
