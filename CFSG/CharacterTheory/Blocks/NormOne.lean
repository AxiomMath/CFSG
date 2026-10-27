module

public import CFSG.CharacterTheory.Blocks.VirtualCharacterCoefficients
public import CFSG.CharacterTheory.TwoRankLowerBound.VirtualNormOne

public noncomputable section

namespace CFSG

open TwoRankLowerBound.Helpers
open scoped BigOperators Classical

theorem blocksVChar_norm_one_signed_irreducible {G : Type} [Group G] [Fintype G]
    {f : G → ℂ} (hf : f ∈ BlocksVChar G) (hnorm : BlocksInnerProduct f f = 1) :
    ∃ χ : BlocksIrr G, f = (χ : G → ℂ) ∨ f = -(χ : G → ℂ) := by
  obtain ⟨n, hn, _⟩ := blocksVChar_exists_unique_expansion hf
  have hsum : (∑ χ ∈ n.support, n χ ^ 2 : ℤ) = 1 := by
    apply Int.cast_injective (α := ℂ)
    rw [Int.cast_one, ← blocksInnerProduct_expansion_norm, hn]
    exact hnorm
  have hsum' : (∑ χ : n.support, n χ.val ^ 2 : ℤ) = 1 := by
    rwa [Finset.sum_subtype n.support (by intros; rfl)] at hsum
  obtain ⟨χ, hsign, houtside⟩ := integer_norm_one_single_coefficient
    (fun χ : n.support => n χ.val) hsum'
  have heq : f = (n χ.val : ℂ) • (χ.val : G → ℂ) := by
    rw [← hn]
    funext x
    rw [blocksCharacterExpansion_apply]
    change (∑ ψ ∈ n.support, (n ψ : ℂ) * (ψ : G → ℂ) x) = _
    rw [Finset.sum_eq_single χ.val]
    · rfl
    · intro ψ hψ hne
      have hzero : n ψ = 0 := houtside ⟨ψ, hψ⟩ (by
        intro hequal
        exact hne (congrArg Subtype.val hequal))
      rw [hzero, Int.cast_zero, zero_mul]
    · exact fun hnot => (hnot χ.property).elim
  refine ⟨χ.val, ?_⟩
  rcases hsign with hpos | hneg
  · exact Or.inl (by simpa only [hpos, Int.cast_one, one_smul] using heq)
  · exact Or.inr (by simpa only [hneg, Int.cast_neg, Int.cast_one, neg_one_smul] using heq)

theorem blocksIrr_identity_normSq_ge_one {G : Type} [Group G] (χ : BlocksIrr G) :
    1 ≤ Complex.normSq ((χ : G → ℂ) 1) := by
  have hχ := (Set.ext_iff.mp (blocksIrr_eq_irreducible_characters G) (χ : G → ℂ)).mp
    χ.property
  obtain ⟨ρ, hρ, hρχ⟩ := hχ
  have hdim : 0 < Module.finrank ℂ ρ.vector := by
    apply Nat.pos_of_ne_zero
    intro hzero
    apply irreducible_character_degree_ne_zero ρ hρ
    rw [FiniteComplexRepresentation.character, Representation.char_one, hzero, Nat.cast_zero]
  rw [← hρχ, FiniteComplexRepresentation.character, Representation.char_one,
    Complex.normSq_natCast]
  have hdim' : (1 : ℝ) ≤ Module.finrank ℂ ρ.vector := by exact_mod_cast hdim
  nlinarith

theorem blocksVChar_norm_one_identity_bound {G : Type} [Group G] [Fintype G]
    {f : G → ℂ} (hf : f ∈ BlocksVChar G) (hnorm : BlocksInnerProduct f f = 1) :
    1 ≤ ‖f 1‖ ^ 2 := by
  rw [Complex.sq_norm]
  obtain ⟨χ, hpos | hneg⟩ := blocksVChar_norm_one_signed_irreducible hf hnorm
  · rw [hpos]
    exact blocksIrr_identity_normSq_ge_one χ
  · rw [hneg, Pi.neg_apply, Complex.normSq_neg]
    exact blocksIrr_identity_normSq_ge_one χ

end CFSG
