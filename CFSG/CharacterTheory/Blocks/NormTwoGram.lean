module

public import CFSG.CharacterTheory.Blocks.NormTwoCommonSign

public noncomputable section

namespace CFSG

open scoped Classical

theorem blocksVChar_norm_two_gram_common_sign
    {G index : Type} [Group G] [Fintype G] [Nonempty index]
    (f : index → G → ℂ) (hf : ∀ i, f i ∈ BlocksVChar G)
    (hdegree : ∀ i, f i 1 = 0)
    (hgram : ∀ i j, BlocksInnerProduct (f i) (f j) =
      1 + if i = j then 1 else 0) :
    ∃ (common : BlocksIrr G) (χ : index → BlocksIrr G) (ε : ℤ),
      Function.Injective χ ∧ (∀ i, χ i ≠ common) ∧ (ε = 1 ∨ ε = -1) ∧
      (∀ i, (χ i : G → ℂ) 1 = (common : G → ℂ) 1) ∧
      ∀ i, f i = (ε : ℂ) • ((χ i : G → ℂ) - (common : G → ℂ)) := by
  have hnorm (i : index) : BlocksInnerProduct (f i) (f i) = 2 := by
    simpa only [↓reduceIte, one_add_one_eq_two] using hgram i i
  have hfinjective : Function.Injective f := by
    intro i j hequal
    by_contra hne
    have hpair := hgram i j
    rw [hequal, hnorm j] at hpair
    norm_num [hne] at hpair
  choose a b hab hdeg hrepresentation using fun i =>
    blocksVChar_degree_zero_norm_two_difference (hf i) (hnorm i) (hdegree i)
  have hshare (i j : index) (hne : i ≠ j) : a i = a j ∨ b i = b j := by
    apply blocksIrr_differences_share_of_pairing_one
    rw [← hrepresentation i, ← hrepresentation j]
    simpa only [hne, ↓reduceIte, add_zero] using hgram i j
  rcases pairwise_shared_pairs_have_common_coordinate a b hshare with
    ⟨common, hcommon⟩ | ⟨common, hcommon⟩
  · refine ⟨common, b, -1, ?_, ?_, Or.inr rfl, ?_, ?_⟩
    · intro i j hequal
      apply hfinjective
      rw [hrepresentation i, hrepresentation j, hcommon i, hcommon j, hequal]
    · intro i hequal
      exact hab i ((hcommon i).trans hequal.symm)
    · intro i
      simpa only [← hcommon i] using (hdeg i).symm
    · intro i
      simp only [Int.cast_neg, Int.cast_one, neg_one_smul, neg_sub]
      rw [hrepresentation i, hcommon i]
  · refine ⟨common, a, 1, ?_, ?_, Or.inl rfl, ?_, ?_⟩
    · intro i j hequal
      apply hfinjective
      rw [hrepresentation i, hrepresentation j, hcommon i, hcommon j, hequal]
    · intro i hequal
      exact hab i (hequal.trans (hcommon i).symm)
    · intro i
      simpa only [← hcommon i] using hdeg i
    · intro i
      simp only [Int.cast_one, one_smul]
      rw [hrepresentation i, hcommon i]

end CFSG
