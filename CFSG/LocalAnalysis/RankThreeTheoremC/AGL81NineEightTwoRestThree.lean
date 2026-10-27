module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoEntriesSpor
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoEntriesG28
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoEntriesSpFour
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoEntriesJ3
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoEntriesFive
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoEntriesLinThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoEntriesSeven
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoEntriesFi24

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.AGLEmbedding

theorem kFactNineThreeNoTwoRestThree_holds :
    KFactNineThreeNoTwoRestThree := by
  intro p hp hp2 i hi h2 h3 h4 h5 h6 h7 h8 h9 h10
  cases i with
  | cyclic q hq => exact hi.elim
  | alternating n hn => exact (h3 ⟨n, hn, rfl⟩).elim
  | lie d =>
    rcases hi with ⟨q, hqp, hqe, hd⟩ | ⟨q, hqp, hd⟩ | hsp | ⟨q, hqp, hqe, hd⟩ | ⟨hp3, m, hd⟩ |
      ⟨rfl, ⟨q, hq2, hq3, hd | hd | hd⟩ | ⟨q, hq2, hq2', hd⟩ | ⟨q, hq2, hq1, hd⟩ | hd⟩ |
      ⟨rfl, hd | hd | hd⟩
    · exact (h4 ⟨d, rfl, q, hqp, hqe, hd⟩).elim
    · exact (h5 ⟨d, rfl, q, hqp, hd⟩).elim
    · exact kFactNineThreeNoTwoAt_spFour hp hp2 hsp
    · exact kFactNineThreeNoTwoAt_linThree hp hp2 ⟨q, hqp, hqe, hd⟩
    · exact (h6 ⟨d, rfl, hp3, m, hd⟩).elim
    · exact (h2 ⟨d, rfl, Or.inl ⟨rfl, q, hq2, hq3, hd⟩⟩).elim
    · exact kFactNineThreeNoTwoAt_g28 ⟨q, hq2, hq3, hd⟩
    · exact kFactNineThreeNoTwoAt_sp48 ⟨q, hq2, hq3, hd⟩
    · exact kFactNineThreeNoTwoAt_linThreeFour ⟨q, hq2, hq2', hd⟩
    · exact kFactNineThreeNoTwoAt_sp62 ⟨q, hq2, hq1, hd⟩
    · exact kFactNineThreeNoTwoAt_titsThree hd
    · exact (h2 ⟨d, rfl, Or.inr ⟨rfl, hd⟩⟩).elim
    · exact (h10 ⟨d, rfl, rfl, hd⟩).elim
    · exact kFactNineThreeNoTwoAt_reeF4 hd
  | sporadic s =>
    rcases hi with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ |
      ⟨rfl, rfl⟩
    · exact (h7 ⟨rfl, rfl⟩).elim
    · exact kFactNineThreeNoTwoAt_m12
    · exact kFactNineThreeNoTwoAt_j3
    · exact (h8 ⟨rfl, rfl⟩).elim
    · exact kFactNineThreeNoTwoAt_hs
    · exact kFactNineThreeNoTwoAt_ru
    · exact kFactNineThreeNoTwoAt_onan
    · exact kFactNineThreeNoTwoAt_fi24
    · exact kFactNineThreeNoTwoAt_he
    · exact (h9 ⟨rfl, rfl⟩).elim

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
