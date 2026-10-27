module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3KFactsCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3SporRows
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicOuter
public import CFSG.RankThree.PartOne.KP.BExclusion
public import CFSG.RankThree.PartOne.KP.Fi22Section
public import CFSG.RankThree.PartOne.KP.MSectionMonster
public import CFSG.RankThree.PartOne.KS.FischerSections
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.KlingenSpFour

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.RankThree.PartOne (hasSection_fi23_fi22 hasSection_fi24prime_fi23
  sectionsForceEvenRankFour_B sectionsForceEvenRankFour_Fi22
  sectionsForceEvenRankFour_fi23_fi24prime simplePresentationMHasBSection_holds
  simplePresentationM_sections_of_B_section)


theorem D1CaseThreeKFactsCore3Core.toCore
    (h : D1CaseThreeKFactsCore3Core) :
    D1CaseThreeKFactsCore3 :=
  have h2324 := sectionsForceEvenRankFour_fi23_fi24prime sectionsForceEvenRankFour_Fi22
    hasSection_fi23_fi22 hasSection_fi24prime_fi23
  ⟨h.p1Lie, CFSG.AGLEmbedding.KlingenSpFour.kFactKlingenSpFour, sporCaseThreeKFactsRank3E3_of_rows,
    ⟨CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group, sectionsForceEvenRankFour_Fi22,
      h2324.1, h2324.2, sectionsForceEvenRankFour_B,
      simplePresentationM_sections_of_B_section sectionsForceEvenRankFour_B
        simplePresentationMHasBSection_holds⟩,
    CFSG.AGLEmbedding.not_dvd_card_outer_sporadic
      CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
