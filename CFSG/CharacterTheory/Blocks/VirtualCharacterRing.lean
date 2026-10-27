module

public import CFSG.CharacterTheory.Blocks.CharacterCriterion
public import CFSG.CharacterTheory.TwoRankLowerBound.ProductCharacterReconstruction

public section

namespace CFSG

open TwoRankLowerBound.Helpers

theorem blocksVChar_isClassFunction {G : Type} [Group G] [Finite G]
    {f : G → ℂ} (hf : f ∈ BlocksVChar G) : BlocksIsClassFunction f := by
  rw [blocksVChar_eq_virtualCharacters, Submodule.mem_toAddSubgroup] at hf
  exact virtualCharacter_conjugation_invariant f hf

theorem blocksVChar_one (G : Type) [Group G] [Finite G] :
    (1 : G → ℂ) ∈ BlocksVChar G := by
  rw [blocksVChar_eq_virtualCharacters, Submodule.mem_toAddSubgroup,
    ← principalFiniteComplexRepresentation_character G]
  exact character_mem_virtualCharacters _

theorem blocksVChar_mul {G : Type} [Group G] [Finite G]
    {f g : G → ℂ} (hf : f ∈ BlocksVChar G) (hg : g ∈ BlocksVChar G) :
    f * g ∈ BlocksVChar G := by
  rw [blocksVChar_eq_virtualCharacters, Submodule.mem_toAddSubgroup] at hf hg ⊢
  exact virtualCharacters_mul f g hf hg

@[expose] def blocksVCharSubring (G : Type) [Group G] [Finite G] : Subring (G → ℂ) where
  carrier := BlocksVChar G
  zero_mem' := (BlocksVChar G).zero_mem
  add_mem' := (BlocksVChar G).add_mem
  neg_mem' := (BlocksVChar G).neg_mem
  one_mem' := blocksVChar_one G
  mul_mem' := blocksVChar_mul

theorem blocksVChar_comp {G H : Type} [Group G] [Group H] [Finite G] [Finite H]
    (homomorphism : H →* G) {f : G → ℂ} (hf : f ∈ BlocksVChar G) :
    f ∘ homomorphism ∈ BlocksVChar H := by
  rw [blocksVChar_eq_virtualCharacters, Submodule.mem_toAddSubgroup] at hf ⊢
  exact inflation_mem_virtualCharacters homomorphism hf

theorem blocksVChar_restrict {G : Type} [Group G] [Finite G]
    (H : Subgroup G) {f : G → ℂ} (hf : f ∈ BlocksVChar G) :
    (fun h : H => f h) ∈ BlocksVChar H := by
  simpa only [Function.comp_def, Subgroup.subtype_apply] using blocksVChar_comp H.subtype hf

end CFSG
