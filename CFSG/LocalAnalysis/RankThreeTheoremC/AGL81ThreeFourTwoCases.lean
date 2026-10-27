module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

theorem kFactThreeFourTwo_of_cases (hL2 : ThreeFourTwoLinTwo) (hU3 : ThreeFourTwoUnitary)
    (hSp4 : ThreeFourTwoSpFour) (hL3 : ThreeFourTwoLinThree) (hRee : ThreeFourTwoReeTwo)
    (h3L : ThreeFourTwoThreeLie) (h3P : ThreeFourTwoThreePairs) (h3A : ThreeFourTwoThreeAlt)
    (h3S : ThreeFourTwoThreeSporadic) (h3Sq : ThreeFourTwoLTwoEightSq)
    (h5L : ThreeFourTwoFiveLie) (hA10 : ThreeFourTwoAltTen)
    (hSN : ThreeFourTwoSporadicNone) (hSP : ThreeFourTwoSporadicPairs)
    (hSzSq : ThreeFourTwoSzSq) : KFactThreeFourTwo := by
  intro p Y _ _ K Y₀ E R I T _ _ _ σ ψ hp hp2 hKY hK hlist
  suffices h : ∃ (X : Type) (_ : Group X), ThreeFourTwoAt p X ∧ Nonempty (K ≃* X) by
    obtain ⟨X, _, hX, he⟩ := h
    exact hX Y K Y₀ E R I T σ ψ hp hp2 hK he
  rcases hlist with ⟨i, hi, he⟩ | ⟨d, hd, he⟩
  · rcases i with ⟨_, _⟩ | ⟨n, hn⟩ | d | s
    · exact hi.elim
    · rcases hi with ⟨rfl, h69⟩ | ⟨rfl, rfl⟩
      · exact ⟨_, _, (h3A n hn h69).threeFourTwoAt, he⟩
      · exact ⟨_, _, hA10 hn, he⟩
    · rcases hi with ⟨q, hqp, hq2, hd⟩ | ⟨q, hqp, hd⟩ |
        ⟨q, ⟨hqp, hq1, hd⟩ | ⟨rfl, hq2, hq1, hd⟩⟩ | ⟨q, hqp, hq1, hd⟩ | ⟨rfl, m, hd⟩ |
        ⟨rfl, h3⟩ | ⟨rfl, h5⟩
      · exact ⟨_, _, (hL2 p hp hp2 q d hqp hq2 hd).threeFourTwoAt, he⟩
      · exact ⟨_, _, (hU3 p hp hp2 q d hqp hd).threeFourTwoAt, he⟩
      · exact ⟨_, _, (hSp4.1 p hp hp2 q d hqp hq1 hd).threeFourTwoAt, he⟩
      · exact ⟨_, _, (hSp4.2 q d hq2 hq1 hd).threeFourTwoAt, he⟩
      · exact ⟨_, _, (hL3 p hp hp2 q d hqp hq1 hd).threeFourTwoAt, he⟩
      · exact ⟨_, _, (hRee m d hd).threeFourTwoAt, he⟩
      · rcases h3 with ⟨q, hq2, hq3, hd | hd | hd⟩ | ⟨q, hq2, hq4, hd⟩ | ⟨q, hq2, hq1, hd⟩ | hd
        · exact ⟨_, _, (h3L q d hq2 (.inl ⟨hq3, hd⟩)).threeFourTwoAt, he⟩
        · exact ⟨_, _, h3P d (.inl ⟨q, hq2, .inl ⟨hq3, .inl hd⟩⟩), he⟩
        · exact ⟨_, _, h3P d (.inl ⟨q, hq2, .inl ⟨hq3, .inr hd⟩⟩), he⟩
        · exact ⟨_, _, (h3L q d hq2 (.inr ⟨hq4, hd⟩)).threeFourTwoAt, he⟩
        · exact ⟨_, _, h3P d (.inl ⟨q, hq2, .inr ⟨hq1, hd⟩⟩), he⟩
        · exact ⟨_, _, h3P d (.inr hd), he⟩
      · exact ⟨_, _, (h5L d h5).threeFourTwoAt, he⟩
    · rcases hi with ⟨rfl, h⟩ | ⟨rfl, h | h | h⟩ | ⟨rfl, h | h | h⟩ | ⟨rfl, rfl⟩
      · exact ⟨_, _, (h3S s h).threeFourTwoAt, he⟩
      · exact ⟨_, _, (hSN.1 s (.inl h)).threeFourTwoAt, he⟩
      · subst h
        exact ⟨_, _, hSP.1, he⟩
      · exact ⟨_, _, (hSN.1 s (.inr h)).threeFourTwoAt, he⟩
      · exact ⟨_, _, hSP.2 s (.inl h)
          ((hKY.subgroup K).of_injective he.some.symm.toMonoidHom he.some.symm.injective), he⟩
      · exact ⟨_, _, hSP.2 s (.inr h)
          ((hKY.subgroup K).of_injective he.some.symm.toMonoidHom he.some.symm.injective), he⟩
      · subst h
        exact ⟨_, _, hSN.2.1.threeFourTwoAt, he⟩
      · exact ⟨_, _, hSN.2.2.threeFourTwoAt, he⟩
  · rcases hd with ⟨rfl, q, hq2, hq3, hd⟩ | ⟨rfl, hd⟩
    · exact ⟨_, _, (h3Sq q d hq2 hq3 hd).threeFourTwoAt, he⟩
    · exact ⟨_, _, (hSzSq d hd).threeFourTwoAt, he⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
