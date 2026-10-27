module

public import CFSG.CharacterTheory.BlockSectionOrthogonality.GroupAlgebraSpectral
public import CFSG.CharacterTheory.BlockSectionOrthogonality.PermutationTrace

public section

open CFSG
namespace CFSG.BlockSectionOrthogonality.Helpers

attribute [local instance] Classical.decEq

@[expose] noncomputable def leftMultiplicationMatrix {G : Type} [Group G] [Fintype G]
    (element : MonoidAlgebra ℂ G) : Matrix G G ℂ :=
  fun row column => element.coeff (row * column⁻¹)

theorem leftMultiplicationMatrix_eq_toMatrix {G : Type} [Group G] [Fintype G]
    (element : MonoidAlgebra ℂ G) :
    leftMultiplicationMatrix element =
      LinearMap.toMatrix (MonoidAlgebra.basis G ℂ) (MonoidAlgebra.basis G ℂ)
        (Algebra.lmul ℂ (MonoidAlgebra ℂ G) element) := by
  ext row column
  rw [LinearMap.toMatrix_apply]
  change element.coeff (row * column⁻¹) =
    ((MonoidAlgebra.basis G ℂ).repr
      ((Algebra.lmul ℂ (MonoidAlgebra ℂ G) element) ((MonoidAlgebra.basis G ℂ) column))) row
  rw [MonoidAlgebra.basis_apply]
  change element.coeff (row * column⁻¹) =
    ((MonoidAlgebra.basis G ℂ).repr (element * MonoidAlgebra.single column 1)) row
  change element.coeff (row * column⁻¹) =
    (element * MonoidAlgebra.single column 1).coeff row
  rw [MonoidAlgebra.coeff_mul_single_apply, mul_one]

theorem leftMultiplicationMatrix_mul {G : Type} [Group G] [Fintype G]
    (left right : MonoidAlgebra ℂ G) :
    leftMultiplicationMatrix (left * right) =
      leftMultiplicationMatrix left * leftMultiplicationMatrix right := by
  rw [leftMultiplicationMatrix_eq_toMatrix, leftMultiplicationMatrix_eq_toMatrix,
    leftMultiplicationMatrix_eq_toMatrix, map_mul, LinearMap.toMatrix_mul]

theorem leftMultiplicationMatrix_commutes_twoSided {G : Type} [Group G] [Fintype G]
    (element : MonoidAlgebra ℂ G)
    (hCentral : ∀ basisElement, element * basisElement = basisElement * element) (left right : G) :
    leftMultiplicationMatrix element * permutationMatrix (twoSidedPermutation left right) =
      permutationMatrix (twoSidedPermutation left right) * leftMultiplicationMatrix element := by
  ext row column
  rw [matrix_mul_permutationMatrix, permutationMatrix_mul_matrix]
  change element.coeff (row * (left * column * right⁻¹)⁻¹) =
    element.coeff ((left⁻¹ * row * right) * column⁻¹)
  have hCentralLeft := congrArg (fun coefficient : MonoidAlgebra ℂ G => coefficient.coeff
    (row * right * column⁻¹)) (hCentral (MonoidAlgebra.single left 1))
  rw [MonoidAlgebra.coeff_mul_single_apply, MonoidAlgebra.coeff_single_mul_apply,
    mul_one, one_mul] at hCentralLeft
  simpa only [mul_inv_rev, inv_inv, mul_assoc] using hCentralLeft

theorem block_twoSided_matrix_trace {G : Type} [Group G] [Fintype G]
    (characters : Set (G → ℂ)) (hFinite : characters.Finite)
    (hSubset : characters ⊆ BlocksIrr G) (left right : G) :
    (leftMultiplicationMatrix (setIdempotent characters hFinite) *
      permutationMatrix (twoSidedPermutation left right)).trace =
        ∑ᶠ character ∈ characters, character left * character right⁻¹ := by
  classical
  change (∑ element, (leftMultiplicationMatrix (setIdempotent characters hFinite) *
    permutationMatrix (ring := ℂ) (twoSidedPermutation left right)) element element) = _
  simp_rw [matrix_mul_permutationMatrix]
  change (∑ element, (setIdempotent characters hFinite).coeff
    (element * (left * element * right⁻¹)⁻¹)) = _
  simp_rw [setIdempotent_coeff, BlocksIdempotentCoeff,
    finsum_mem_eq_finite_toFinset_sum _ hFinite]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro character hCharacter
  have hIrr := hSubset (hFinite.mem_toFinset.mp hCharacter)
  rcases hIrr with ⟨space, hAdd, hModule, hDimension, representation, hIrreducible, rfl⟩
  let := hIrreducible
  simp only [mul_inv_rev, inv_inv, mul_assoc]
  rw [← Finset.mul_sum]
  have hAverage := sum_character_conjugates representation left right⁻¹
  simp only [mul_assoc] at hAverage
  rw [hAverage]
  have hCard : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hDegree := irreducible_character_one_ne_zero representation
  field_simp

end CFSG.BlockSectionOrthogonality.Helpers
