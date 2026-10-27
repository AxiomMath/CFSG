module

public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterExpansion

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem characterPairing_virtual_irreducible_integer {G : Type*} [Group G] [Fintype G]
    (function : G → ℂ) (hvirtual : function ∈ virtualCharacters G)
    (data : FiniteComplexRepresentation G) (hirreducible : data.IsIrreducible) :
    ∃ integer : ℤ, characterPairing function data.character = integer := by
  obtain ⟨expansion⟩ := virtualCharacter_exists_irreducibleCharacterExpansion hvirtual
  refine ⟨∑ label : expansion.index,
    if (expansion.representation label).character = data.character then expansion.coefficient label else 0, ?_⟩
  conv_lhs => arg 1; rw [funext expansion.expansion]
  rw [characterPairing_expansion_left]
  simp_rw [characterPairing_irreducible _ _ (expansion.irreducible _) hirreducible]
  simp only [Int.cast_sum, Int.cast_ite, Int.cast_zero, mul_ite, mul_one, mul_zero]

theorem characterPairing_virtual_integer {G : Type*} [Group G] [Fintype G]
    (left right : G → ℂ) (hleft : left ∈ virtualCharacters G) (hright : right ∈ virtualCharacters G) :
    ∃ integer : ℤ, characterPairing left right = integer := by
  obtain ⟨expansion⟩ := virtualCharacter_exists_irreducibleCharacterExpansion hright
  choose integer hinteger using (fun label : expansion.index =>
    characterPairing_virtual_irreducible_integer left hleft (expansion.representation label)
      (expansion.irreducible label))
  refine ⟨∑ label, expansion.coefficient label * integer label, ?_⟩
  conv_lhs => arg 2; rw [funext expansion.expansion]
  rw [characterPairing_expansion_right]
  simp only [hinteger, Int.cast_sum, Int.cast_mul]

theorem characterPairing_virtual_principal_integer {G : Type*} [Group G] [Fintype G]
    (function : G → ℂ) (hvirtual : function ∈ virtualCharacters G) :
    ∃ integer : ℤ, characterPairing function 1 = integer := by
  have hpair := characterPairing_virtual_irreducible_integer function hvirtual
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  simpa only [principalFiniteComplexRepresentation_character] using hpair

end CFSG.TwoRankLowerBound.Helpers
