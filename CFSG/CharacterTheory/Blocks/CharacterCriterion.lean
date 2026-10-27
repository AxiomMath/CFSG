module

public import CFSG.CharacterTheory.Blocks.Defs
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerElementary
public import CFSG.CharacterTheory.TwoRankLowerBound.VirtualCharacters

public section

namespace CFSG

open TwoRankLowerBound.Helpers

theorem blocksIrr_eq_irreducible_characters (G : Type) [Group G] :
    BlocksIrr G = {character | ∃ data : FiniteComplexRepresentation.{0, 0} G,
      data.IsIrreducible ∧ data.character = character} := by
  ext character
  constructor
  · rintro ⟨V, hAdd, hModule, hFinite, representation, hirreducible, hcharacter⟩
    let data : FiniteComplexRepresentation.{0, 0} G :=
      { vector := V
        addCommGroup := hAdd
        module := hModule
        finiteDimensional := hFinite
        representation := representation }
    exact ⟨data, hirreducible, hcharacter⟩
  · rintro ⟨data, hirreducible, hcharacter⟩
    exact ⟨data.vector, data.addCommGroup, data.module, data.finiteDimensional,
      data.representation, hirreducible, hcharacter⟩

theorem blocksVChar_eq_virtualCharacters (G : Type) [Group G] [Finite G] :
    BlocksVChar G = (virtualCharacters G).toAddSubgroup := by
  rw [virtualCharacters_eq_irreducible, irreducibleVirtualCharacters,
    ← blocksIrr_eq_irreducible_characters, Submodule.span_int_eq_addSubgroupClosure]
  rfl

theorem blocksBrauerElementary_iff (G : Type*) [Group G] :
    BlocksBrauerElementary G ↔ BrauerElementary G := by
  constructor
  · rintro ⟨prime, hprime, cyclic, primary, hcyclic, hcoprime, hprimary,
      hcommute, hproduct⟩
    let commute : ∀ first : cyclic, ∀ second : primary,
        Commute (first : G) (second : G) :=
      fun first second => hcommute first first.property second second.property
    refine ⟨prime, cyclic, primary, hprime, hcyclic, hcoprime, hprimary, commute, ?_⟩
    intro element
    obtain ⟨first, hfirst, second, hsecond, helement⟩ := hproduct element
    exact ⟨(⟨first, hfirst⟩, ⟨second, hsecond⟩), helement.symm⟩
  · rintro ⟨prime, cyclic, primary, hprime, hcyclic, hcoprime, hprimary,
      hcommute, hproduct⟩
    refine ⟨prime, hprime, cyclic, primary, hcyclic, hcoprime, hprimary, ?_, ?_⟩
    · intro first hfirst second hsecond
      exact hcommute ⟨first, hfirst⟩ ⟨second, hsecond⟩
    · intro element
      obtain ⟨⟨first, second⟩, helement⟩ := hproduct element
      exact ⟨first, first.property, second, second.property, helement.symm⟩

end CFSG
