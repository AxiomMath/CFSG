module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeKFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1Alt
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericListPrune3
import CFSG.RankThree.PartOne.KP.Fi22Section
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Seed.Fi22

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

theorem kFactSevenFive_holds :
    KFactSevenFive := by
  intro G _ _ he p i hi hs H φ hφ
  rcases hi with ⟨hp7, hn, rfl⟩ | ⟨hp5, hn, rfl⟩ | ⟨-, rfl⟩
  · exact CFSG.LocalAnalysis.RankThreeTheoremC.false_of_section_alternating he (by omega) φ hφ
  · exact CFSG.LocalAnalysis.RankThreeTheoremC.false_of_section_alternating he (by omega) φ hφ
  · haveI : IsSimpleGroup (↥H ⧸ φ.ker) :=
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ).isSimpleGroup_congr.mpr hs
    exact CFSG.LocalAnalysis.RankThreeTheoremC.false_of_section_fi22 he
      CFSG.RankThree.PartOne.sectionsForceEvenRankFour_Fi22
      (fun h => @CFSG.QuasithinUnique.SQTK.nonempty_mulEquiv_carrier_Fi22 h) inferInstance
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
