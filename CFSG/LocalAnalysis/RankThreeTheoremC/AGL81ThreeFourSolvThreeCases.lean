module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

theorem kFactThreeFourSolvThree_of_cases (hL2 : ThreeFourSolvThreeLinTwo)
    (hU3 : ThreeFourSolvThreeUnitary) (hL3 : ThreeFourSolvThreeLinThree)
    (hRee : ThreeFourSolvThreeReeTwo) (hLie : ThreeFourSolvThreeLie)
    (hSpor : ThreeFourSolvThreeSporadic) (hSq : ThreeFourSolvThreeLTwoEightSq)
    (hT : ThreeFourSolvThreeTargets) : KFactThreeFourSolvThree := by
  intro Y _ _ K Y₀ E R I₀ _ _ σ hK hlist
  suffices h : ∃ (X : Type) (_ : Group X), ThreeFourSolvThreeAt X ∧ Nonempty (K ≃* X) by
    obtain ⟨X, _, hX, he⟩ := h
    exact hX Y K Y₀ E R I₀ σ hK he
  rcases hlist with ⟨i, hi, he⟩ | ⟨d, hd, he⟩
  · rcases i with ⟨_, _⟩ | ⟨n, hn⟩ | d | s
    · exact hi.elim
    · rcases hi with ⟨-, h69⟩ | ⟨h, -⟩
      · refine ⟨_, _, (hT.1 n hn h69).at fun K _ hK => ?_, he⟩
        rcases h69 with rfl | rfl
        · exact Or.inl hK
        · exact Or.inr (Or.inr (Or.inr hK))
      · exact absurd h (by decide)
    · rcases hi with ⟨q, hqp, hq2, hd⟩ | ⟨q, hqp, hd⟩ |
        ⟨q, ⟨hqp, hq1, hd⟩ | ⟨-, hq2, hq1, hd⟩⟩ | ⟨q, hqp, hq1, hd⟩ | ⟨-, m, hd⟩ |
        ⟨-, h3⟩ | ⟨h, -⟩
      · exact ⟨_, _, (hL2 q d hqp hq2 hd).at, he⟩
      · exact ⟨_, _, (hU3 q d hqp hd).at, he⟩
      ·
        exfalso
        have hv := ((TauCeti.LieTypeIndex.valid_iff _).mp d.2).2
        rw [hd, TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at hv
        have hcard : q.card = 3 := by rw [TauCeti.PrimePower.card_def, hqp, hq1]; norm_num
        exact hv ⟨rfl, hcard⟩
      · exact ⟨_, _, (hT.2 q d hq2 hq1 (.inl hd)).at fun K _ hK =>
          Or.inr (Or.inl ⟨d, ⟨q, hq2, hq1, hd⟩, hK⟩), he⟩
      · exact ⟨_, _, (hL3 q d hqp hq1 hd).at, he⟩
      · exact ⟨_, _, (hRee m d hd).at, he⟩
      · rcases h3 with ⟨q, hq2, hq3, hd⟩ | ⟨q, hq2, hq4, hd⟩ | ⟨q, hq2, hq1, hd⟩ | hd
        · exact ⟨_, _, (hLie d (.inl ⟨q, hq2, .inl ⟨hq3, hd⟩⟩)).at, he⟩
        · exact ⟨_, _, (hLie d (.inl ⟨q, hq2, .inr ⟨hq4, hd⟩⟩)).at, he⟩
        · exact ⟨_, _, (hT.2 q d hq2 hq1 (.inr hd)).at fun K _ hK =>
            Or.inr (Or.inr (Or.inl ⟨d, ⟨q, hq2, hq1, hd⟩, hK⟩)), he⟩
        · exact ⟨_, _, (hLie d (.inr hd)).at, he⟩
      · exact absurd h (by decide)
    · rcases hi with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact ⟨_, _, (hSpor s h).at, he⟩
      all_goals exact absurd h (by decide)
  · rcases hd with ⟨-, q, hq2, hq3, hd⟩ | ⟨h, -⟩
    · exact ⟨_, _, (hSq q d hq2 hq3 hd).at, he⟩
    · exact absurd h (by decide)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
