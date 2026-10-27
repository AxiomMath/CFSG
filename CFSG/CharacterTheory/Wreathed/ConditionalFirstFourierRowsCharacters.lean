module

public import CFSG.CharacterTheory.Wreathed.ConditionalFourierParityCharacters

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.ConditionalFirstFourierRows

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.ConditionalFourier

variable {G : Type} [Group G] [Fintype G] {basis : FiniteIrreducibleCharacterBasis G}

theorem blocksInnerProduct_basisCombination_character {B : Finset basis.index}
    {φ : basis.index} (hφ : φ ∈ B) (e : basis.index → ℤ) :
    BlocksInnerProduct (basisCombination basis B e) (basis.representation φ).character =
      e φ := by
  rw [← basisCombination_unitVector B hφ, blocksInnerProduct_basisCombination,
    sum_mul_unitVector hφ]

theorem eq_of_basisCombination_eq {B : Finset basis.index} {e e' : basis.index → ℤ}
    (h : basisCombination basis B e = basisCombination basis B e') {φ : basis.index}
    (hφ : φ ∈ B) : e φ = e' φ := by
  have h' := congrArg (fun F => BlocksInnerProduct F (basis.representation φ).character) h
  simp only [blocksInnerProduct_basisCombination_character hφ] at h'
  exact_mod_cast h'

end CFSG.Wreathed.ConditionalFirstFourierRows
