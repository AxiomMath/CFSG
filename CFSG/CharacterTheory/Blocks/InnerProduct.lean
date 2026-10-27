module

public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterConjugateInverse
public import CFSG.CharacterTheory.Blocks.CharacterCriterion

public section

namespace CFSG

open TwoRankLowerBound.Helpers
open scoped BigOperators Classical

@[expose] noncomputable def BlocksInnerProduct {G : Type} [Group G] [Fintype G]
    (f g : G → ℂ) : ℂ :=
  (Nat.card G : ℂ)⁻¹ * ∑ x : G, f x * starRingEnd ℂ (g x)

theorem blocksVChar_conjugate_inverse {G : Type} [Group G] [Finite G]
    {f : G → ℂ} (hf : f ∈ BlocksVChar G) (x : G) :
    starRingEnd ℂ (f x) = f x⁻¹ := by
  rw [blocksVChar_eq_virtualCharacters, Submodule.mem_toAddSubgroup] at hf
  exact virtual_character_conjugate_inverse f hf x

theorem blocksInnerProduct_eq_characterPairing {G : Type} [Group G] [Fintype G]
    (f : G → ℂ) {g : G → ℂ} (hg : g ∈ BlocksVChar G) :
    BlocksInnerProduct f g = characterPairing f g := by
  simp only [BlocksInnerProduct, characterPairing, blocksVChar_conjugate_inverse hg]

theorem blocksInnerProduct_inducedFunction_left {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) (α : H → ℂ) (β : G → ℂ) (hβ : BlocksIsClassFunction β) :
    BlocksInnerProduct (inducedFunction H α) β =
      BlocksInnerProduct α (fun h : H => β h) := by
  let inverseConjugate : G → ℂ := fun x => starRingEnd ℂ (β x⁻¹)
  have hinvariant : BlocksIsClassFunction inverseConjugate := by
    intro x y
    dsimp [inverseConjugate]
    simp only [mul_inv_rev, inv_inv, mul_assoc]
    rw [← mul_assoc y x⁻¹ y⁻¹, hβ x⁻¹ y]
  simpa only [BlocksInnerProduct, characterPairing, inverseConjugate, inv_inv,
    Subgroup.coe_inv] using
    characterPairing_inducedFunction_left H α inverseConjugate hinvariant

theorem blocks_induction_projection_formula {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) (α : H → ℂ) (β : G → ℂ) (hβ : BlocksIsClassFunction β) :
    β * inducedFunction H α = inducedFunction H (fun h => β h * α h) :=
  inducedFunction_projection_formula H α β hβ

theorem blocksInnerProduct_virtual_integer {G : Type} [Group G] [Fintype G]
    {α β : G → ℂ} (hα : α ∈ BlocksVChar G) (hβ : β ∈ BlocksVChar G) :
    ∃ n : ℤ, BlocksInnerProduct α β = n := by
  rw [blocksInnerProduct_eq_characterPairing α hβ]
  rw [blocksVChar_eq_virtualCharacters, Submodule.mem_toAddSubgroup] at hα hβ
  exact characterPairing_virtual_integer α β hα hβ

end CFSG
