module

public import CFSG.LocalAnalysis.SectionRank.QTK.Interface
import CFSG.RankThree.PartTwo.Sec4.Census.Alternating46

public section

namespace CFSG.SectionRank.QTK

theorem qtAltRestriction_holds : QTAltRestriction := by
  intro S _ _ n hQT ⟨e⟩
  by_contra h9
  exact not_evenRank_le_two_of_localRank e Nat.prime_three (by norm_num)
    (CFSG.RankThree.PartTwo.Sec4.Census.three_le_localRank_alternating (by omega)) hQT

end CFSG.SectionRank.QTK
