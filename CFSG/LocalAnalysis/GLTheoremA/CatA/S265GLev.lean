module

public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalLevels
public import CFSG.Timmesfeld.Orders.ExceptionalWeylCert

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265G

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.EvenOddRadical
open CFSG.Timmesfeld.ExceptionalOrders

theorem parabolicDegree_maskSet {τ : Tag} (m : ℕ) (α : Fin τ.rank → ℤ) :
    parabolicDegree τ (maskSet τ m : Set (Fin τ.rank)) α =
      ∑ i, if m.testBit i.val = true then 0 else α i := by
  unfold parabolicDegree
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Finset.mem_coe, mem_maskSet]

theorem levelRoots_maskSet {τ : Tag} (m : ℕ) (d : ℤ) :
    levelRoots τ (maskSet τ m : Set (Fin τ.rank)) d =
      {α | IsRoot τ α ∧ (0 < height α ∧ d ≤ ∑ i, if m.testBit i.val = true then 0 else α i)} := by
  ext α
  simp only [levelRoots, Set.mem_setOf_eq, parabolicDegree_maskSet]


theorem ncard_levelRoots_seven :
    (levelRoots .F4 (maskSet .F4 7 : Set (Fin Tag.F4.rank)) 1).ncard = 15 := by
  rw [levelRoots_maskSet, ncard_setOf_isRoot_and]
  decide +kernel

theorem ncard_levelRoots_fourteen :
    (levelRoots .F4 (maskSet .F4 14 : Set (Fin Tag.F4.rank)) 1).ncard = 15 := by
  rw [levelRoots_maskSet, ncard_setOf_isRoot_and]
  decide +kernel

theorem ncard_levelRoots_eleven :
    (levelRoots .F4 (maskSet .F4 11 : Set (Fin Tag.F4.rank)) 3).ncard = 5 := by
  rw [levelRoots_maskSet, ncard_setOf_isRoot_and]
  decide +kernel

private theorem fin_four_cases (i : Fin Tag.F4.rank) :
    i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ ∨ i = ⟨2, by decide⟩ ∨ i = ⟨3, by decide⟩ := by
  obtain ⟨i, hi⟩ := i
  change i < 4 at hi
  interval_cases i <;> simp

theorem subset_or_eq_thirteen {J : Set (Fin Tag.F4.rank)} (hJ : J ≠ Set.univ) :
    J ⊆ (maskSet .F4 7 : Set (Fin Tag.F4.rank)) ∨ J ⊆ (maskSet .F4 14 : Set (Fin Tag.F4.rank)) ∨
      J ⊆ (maskSet .F4 11 : Set (Fin Tag.F4.rank)) ∨
        J = (maskSet .F4 13 : Set (Fin Tag.F4.rank)) := by
  by_cases h3 : (⟨3, by decide⟩ : Fin Tag.F4.rank) ∈ J
  · by_cases h0 : (⟨0, by decide⟩ : Fin Tag.F4.rank) ∈ J
    · by_cases h2 : (⟨2, by decide⟩ : Fin Tag.F4.rank) ∈ J
      ·
        have h1 : (⟨1, by decide⟩ : Fin Tag.F4.rank) ∉ J := by
          intro h1
          refine hJ (Set.eq_univ_of_forall fun i => ?_)
          rcases fin_four_cases i with rfl | rfl | rfl | rfl <;> assumption
        refine Or.inr (Or.inr (Or.inr (Set.ext fun i => ?_)))
        rw [Finset.mem_coe, mem_maskSet]
        rcases fin_four_cases i with rfl | rfl | rfl | rfl
        · exact iff_of_true h0 (by decide)
        · exact iff_of_false h1 (by decide)
        · exact iff_of_true h2 (by decide)
        · exact iff_of_true h3 (by decide)
      · refine Or.inr (Or.inr (Or.inl fun i hi => ?_))
        rw [Finset.mem_coe, mem_maskSet]
        rcases fin_four_cases i with rfl | rfl | rfl | rfl
        · decide
        · decide
        · exact absurd hi h2
        · decide
    · refine Or.inr (Or.inl fun i hi => ?_)
      rw [Finset.mem_coe, mem_maskSet]
      rcases fin_four_cases i with rfl | rfl | rfl | rfl
      · exact absurd hi h0
      · decide
      · decide
      · decide
  · refine Or.inl fun i hi => ?_
    rw [Finset.mem_coe, mem_maskSet]
    rcases fin_four_cases i with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · exact absurd hi h3

end CFSG.LocalAnalysis.GLTheoremA.S265G

end
