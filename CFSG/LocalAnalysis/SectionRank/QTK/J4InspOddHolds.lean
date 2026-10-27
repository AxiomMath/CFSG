module

public import CFSG.LocalAnalysis.SectionRank.QTK.J4InspOddClassical
public import CFSG.LocalAnalysis.SectionRank.QTK.J4InspOddSec
public import CFSG.GroupTheory.LinearPGroup.Rank
public import CFSG.LieType.Chevalley.G2SectionalTwoRank

public section

namespace CFSG.SectionRank.QTK

theorem oddCharSectionalTwoRankQTK_holds :
    OddCharSectionalTwoRankQTK := by
  intro S _ _ hB
  rcases oddCharList_sectionalTwoRankLE_or_G2
      (fun ι _ _ K _ _ h2 => CFSG.LinearPGroup.sectionalTwoRankLE_GL ι K h2) hB with
    h7 | ⟨p, -, hp2, hG2⟩
  · exact h7.mono (by norm_num)
  · exact CFSG.LieType.Chevalley.sectionalTwoRankLE_of_chevalleyExceptionalModel_G2 hp2 hG2

end CFSG.SectionRank.QTK

end
