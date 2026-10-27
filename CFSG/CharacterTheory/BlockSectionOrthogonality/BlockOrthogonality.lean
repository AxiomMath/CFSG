module

public import CFSG.CharacterTheory.BlockSectionOrthogonality.BimoduleTrace
public import CFSG.CharacterTheory.BlockSectionOrthogonality.CharacterInversion

public section

open CFSG
namespace CFSG.BlockSectionOrthogonality.Helpers

attribute [local instance] Classical.decEq

theorem map_permutationMatrix {index : Type*} [Fintype index]
    {source target : Type*} [Semiring source] [Semiring target]
    (homomorphism : source →+* target) (permutation : Equiv.Perm index) :
    homomorphism.mapMatrix (permutationMatrix permutation) = permutationMatrix permutation := by
  ext row column
  simp [RingHom.mapMatrix_apply, permutationMatrix]

theorem localMatrix_eq_of_complex_eq (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    {index : Type*} [Fintype index]
    (left right : Matrix index index (localCoefficientSubring m hm))
    (hEqual : (localCoefficientSubring m hm).subtype.mapMatrix left =
      (localCoefficientSubring m hm).subtype.mapMatrix right) : left = right := by
  ext row column
  exact congrFun (congrFun hEqual row) column

@[expose] noncomputable def admissibleMatrix (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    {G : Type} [Group G] [Fintype G]
    (characters : Set (G → ℂ)) (hCharacters : BlocksAdmissible m G characters) :
    Matrix G G (localCoefficientSubring m hm) :=
  fun row column => ⟨BlocksIdempotentCoeff G characters (row * column⁻¹),
    hCharacters.2 (row * column⁻¹)⟩

theorem admissibleMatrix_complex (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    {G : Type} [Group G] [Fintype G]
    (characters : Set (G → ℂ)) (hCharacters : BlocksAdmissible m G characters)
    (hFinite : characters.Finite) :
    (localCoefficientSubring m hm).subtype.mapMatrix (admissibleMatrix m hm characters hCharacters) =
      leftMultiplicationMatrix (setIdempotent characters hFinite) := by
  ext row column
  exact (setIdempotent_coeff characters hFinite (row * column⁻¹)).symm

theorem admissibleMatrix_isIdempotent (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    {G : Type} [Group G] [Fintype G]
    (characters : Set (G → ℂ)) (hCharacters : BlocksAdmissible m G characters) :
    admissibleMatrix m hm characters hCharacters * admissibleMatrix m hm characters hCharacters =
      admissibleMatrix m hm characters hCharacters := by
  have hFinite := (irreducibles_finite G).subset hCharacters.1
  apply localMatrix_eq_of_complex_eq m hm
  rw [map_mul, admissibleMatrix_complex m hm characters hCharacters hFinite,
    ← leftMultiplicationMatrix_mul, setIdempotent_isIdempotent characters hFinite hCharacters.1]

theorem admissibleMatrix_commutes_twoSided (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    {G : Type} [Group G] [Fintype G]
    (characters : Set (G → ℂ)) (hCharacters : BlocksAdmissible m G characters) (left right : G) :
    admissibleMatrix m hm characters hCharacters * permutationMatrix (twoSidedPermutation left right) =
      permutationMatrix (twoSidedPermutation left right) * admissibleMatrix m hm characters hCharacters := by
  have hFinite := (irreducibles_finite G).subset hCharacters.1
  apply localMatrix_eq_of_complex_eq m hm
  rw [map_mul, map_mul, map_permutationMatrix,
    admissibleMatrix_complex m hm characters hCharacters hFinite]
  exact leftMultiplicationMatrix_commutes_twoSided _
    (setIdempotent_isCentral characters hFinite hCharacters.1) left right

theorem admissible_section_orthogonality (prime : ℕ) (hPrime : prime.Prime)
    (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) (hPrimeMem : (prime : BlocksAlgInt) ∈ m)
    (G : Type) [Group G] [Finite G] (characters : Set (G → ℂ))
    (hCharacters : BlocksAdmissible m G characters)
    (left right leftPrimary rightPrimary : G)
    (hLeft : BlocksIsPPart prime left leftPrimary)
    (hRight : BlocksIsPPart prime right rightPrimary)
    (hNotConjugate : ¬ IsConj leftPrimary rightPrimary) :
    ∑ᶠ character ∈ characters, character left * starRingEnd ℂ (character right) = 0 := by
  classical
  let := Fintype.ofFinite G
  have hFinite := (irreducibles_finite G).subset hCharacters.1
  have hZero := localPermutation_idempotent_trace_zero m hm prime hPrime hPrimeMem
    (twoSidedPermutation left right) (twoSidedPermutation leftPrimary rightPrimary)
    (primaryPart_twoSidedPermutation hPrime hLeft hRight)
    (twoSidedPermutation_no_fixedPoint hNotConjugate)
    (admissibleMatrix m hm characters hCharacters)
    (admissibleMatrix_isIdempotent m hm characters hCharacters)
    (admissibleMatrix_commutes_twoSided m hm characters hCharacters left right)
  have hComplexZero := congrArg (localCoefficientSubring m hm).subtype hZero
  change (localCoefficientSubring m hm).subtype
    (∑ index, (admissibleMatrix m hm characters hCharacters *
      permutationMatrix (ring := localCoefficientSubring m hm)
        (twoSidedPermutation left right)) index index) =
        (localCoefficientSubring m hm).subtype 0 at hComplexZero
  rw [map_sum, map_zero] at hComplexZero
  have hMappedTrace : ((localCoefficientSubring m hm).subtype.mapMatrix
      (admissibleMatrix m hm characters hCharacters *
        permutationMatrix (twoSidedPermutation left right))).trace = 0 := by
    exact hComplexZero
  rw [map_mul, admissibleMatrix_complex m hm characters hCharacters hFinite,
    map_permutationMatrix, block_twoSided_matrix_trace characters hFinite hCharacters.1] at hMappedTrace
  rw [← hMappedTrace]
  apply finsum_mem_congr rfl
  intro character hCharacter
  rw [irreducible_character_inversion (hCharacters.1 hCharacter)]

end CFSG.BlockSectionOrthogonality.Helpers
