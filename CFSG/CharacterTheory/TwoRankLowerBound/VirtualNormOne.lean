module

public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerInduction

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

universe groupUniverse

theorem integer_norm_one_single_coefficient {index : Type*} [Fintype index]
    (coefficient : index → ℤ) (hnorm : ∑ label, coefficient label ^ 2 = 1) :
    ∃ label, (coefficient label = 1 ∨ coefficient label = -1) ∧
      ∀ other, other ≠ label → coefficient other = 0 := by
  have hexists : ∃ label, coefficient label ≠ 0 := by
    by_contra! hzero
    simp only [hzero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero] at hnorm
    exact zero_ne_one hnorm
  obtain ⟨label, hnonzero⟩ := hexists
  have hbound : coefficient label ^ 2 ≤ 1 := by
    rw [← hnorm]
    exact Finset.single_le_sum (fun member _ => sq_nonneg (coefficient member)) (Finset.mem_univ _)
  have hsquare : coefficient label ^ 2 = 1 := by
    have hpositive : 0 < coefficient label ^ 2 := sq_pos_of_ne_zero hnonzero
    omega
  refine ⟨label, sq_eq_one_iff.mp hsquare, ?_⟩
  intro other hne
  have hsum : (∑ member ∈ Finset.univ.erase label, coefficient member ^ 2) = 0 := by
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset index)
      (fun member => coefficient member ^ 2) (Finset.mem_univ label)
    rw [hnorm, hsquare] at hsplit
    omega
  exact (sq_eq_zero_iff).mp ((Finset.sum_eq_zero_iff_of_nonneg
    (fun member _ => sq_nonneg (coefficient member))).mp hsum other
      (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩))

theorem virtual_norm_one_signed_basis_character {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (function : G → ℂ)
    (hvirtual : function ∈ virtualCharacters G) (hnorm : characterPairing function function = 1) :
    ∃ label : basis.index, function = (basis.representation label).character ∨
      function = -(basis.representation label).character := by
  obtain ⟨coefficient, hexpansion, _⟩ := virtualCharacter_basis_integer_expansion basis function hvirtual
  have hsum : (∑ label, coefficient label ^ 2 : ℤ) = 1 := by
    apply Int.cast_injective (α := ℂ)
    rw [Int.cast_sum]
    simp only [Int.cast_pow, Int.cast_one]
    rw [← characterPairing_distinct_expansion_norm basis.representation basis.irreducible basis.distinct]
    change characterPairing (characterBasisIntegerExpansion basis coefficient)
      (characterBasisIntegerExpansion basis coefficient) = 1
    rw [hexpansion]
    exact hnorm
  obtain ⟨label, hsign, houtside⟩ := integer_norm_one_single_coefficient coefficient hsum
  have hequal : function = (coefficient label : ℂ) • (basis.representation label).character := by
    rw [← hexpansion]
    funext element
    change (∑ member, (coefficient member : ℂ) * (basis.representation member).character element) = _
    rw [Finset.sum_eq_single label]
    · rfl
    · intro member _ hne
      rw [houtside member hne, Int.cast_zero, zero_mul]
    · exact fun hnot => (hnot (Finset.mem_univ _)).elim
  refine ⟨label, ?_⟩
  rcases hsign with hpositive | hnegative
  · left
    simpa only [hpositive, Int.cast_one, one_smul] using hequal
  · right
    simpa only [hnegative, Int.cast_neg, Int.cast_one, neg_one_smul] using hequal

theorem character_norm_one_basis_character {G : Type groupUniverse} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G)
    (data : FiniteComplexRepresentation.{groupUniverse, groupUniverse} G)
    (hnorm : characterPairing data.character data.character = 1) :
    ∃ label : basis.index, (basis.representation label).character = data.character := by
  obtain ⟨label, hequal | hequal⟩ := virtual_norm_one_signed_basis_character basis data.character
    (character_mem_virtualCharacters data) hnorm
  · exact ⟨label, hequal.symm⟩
  · have hdegree := congrArg Complex.re (congrFun hequal 1)
    have hpositive : 0 < Module.finrank ℂ (basis.representation label).vector := by
      apply Nat.pos_of_ne_zero
      intro hzero
      apply irreducible_character_degree_ne_zero (basis.representation label) (basis.irreducible label)
      rw [FiniteComplexRepresentation.character, Representation.char_one, hzero, Nat.cast_zero]
    simp only [Pi.neg_apply, FiniteComplexRepresentation.character, Representation.char_one,
      Complex.neg_re, Complex.natCast_re] at hdegree
    have hnonnegative : (0 : ℝ) ≤ Module.finrank ℂ data.vector := Nat.cast_nonneg _
    have hpositiveReal : (0 : ℝ) < Module.finrank ℂ (basis.representation label).vector :=
      Nat.cast_pos.mpr hpositive
    linarith

end CFSG.TwoRankLowerBound.Helpers
