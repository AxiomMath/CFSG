module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourOneDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

theorem five_le_of_prime_of_ne {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) : 5 ≤ p := by
  have h2 := hp.two_le
  by_contra h
  interval_cases p
  · exact hp2 rfl
  · exact hp3 rfl
  · exact absurd hp (by decide)

theorem kFactNineThreeSignalizerThree_of_cases (hL2 : SignalizerThreeLinTwo)
    (hU3 : SignalizerThreeUnitary) (hSp4 : SignalizerThreeSpFour)
    (hL3 : SignalizerThreeLinThree) (hLie5 : SignalizerThreeLieFive)
    (hA10 : SignalizerThreeAltTen) (hSpor : SignalizerThreeSporadic)
    (hSz2 : SignalizerThreeSzSq) : KFactNineThreeSignalizerThree := by
  intro p hp hp2 hp3 K _ _ hK
  have hp5 := five_le_of_prime_of_ne hp hp2 hp3
  rcases hK with ⟨i, hi, he⟩ | ⟨d, hd, he⟩
  · rcases i with ⟨_, _⟩ | ⟨n, hn⟩ | d | s
    · exact hi.elim
    · rcases hi with ⟨rfl, -⟩ | ⟨rfl, rfl⟩
      · exact absurd rfl hp3
      · exact hA10 hn K he
    · rcases hi with ⟨q, hqp, hq2, hd⟩ | ⟨q, hqp, hd⟩ | ⟨q, ⟨hqp, hq1, hd⟩ | ⟨rfl, -⟩⟩ |
        ⟨q, hqp, hq1, hd⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, h5⟩
      · exact hL2 p hp hp5 q d hqp hq2 hd K he
      · exact hU3 p hp hp5 q d hqp hd K he
      · exact hSp4 p hp hp5 q d hqp hq1 hd K he
      · exact absurd rfl hp3
      · exact hL3 p hp hp5 q d hqp hq1 hd K he
      · exact absurd rfl hp3
      · exact absurd rfl hp3
      · exact hLie5 d h5 K he
    · rcases hi with ⟨rfl, -⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, rfl⟩
      · exact absurd rfl hp3
      · exact hSpor.1 s h K he
      · exact hSpor.2.1 s h K he
      · exact hSpor.2.2 K he
  · rcases hd with ⟨rfl, -⟩ | ⟨rfl, hd⟩
    · exact absurd rfl hp3
    · exact hSz2 d hd K he

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
