module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K517_4bOfRankTwoUnitary
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R15Final39
import CFSG.LocalAnalysis.UniquenessCase.UC6K332RowsHolds
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFONoOffender
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15P2GlueHolds
public import CFSG.LocalAnalysis.RankThreeUC.GN15Holds
public import CFSG.LocalAnalysis.RankThreeUC.GN15HoldsFF

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

section CitedInputs41


open CFSG.LocalAnalysis.AGL81TheoremCD in
theorem agl81TheoremDSection15_of_cited_inputs_41
    (hK517rt : K517_4b_rank_two_A2B2G2)
    (hvacL : GN15.FFO.PSLNoOffender)
    (hvacU : GN15.FFO.PSUNoOffender)
    (hD4 : GN15.FFOffenderInvertsOddD4)
    (h1210 : Section14.TwelveTenGen) :
    CFSG.Yardstones.M9cbf837c48cf.AGL81TheoremDSection15Statement :=
  have hS := GN15.ffOffenderInvertsOdd_of_noOffender hvacL hvacU hD4
  agl81TheoremDSection15_of_cited_inputs_39 (K517_4b_of_rank_two_A2B2G2 hK517rt)
    (k5192P2_of_factorShape
      (GN15.s15GNFactorShape_of_JOutCentral (GN15.jOutCentral_of_ffOffender_holds hS)))
    (GN15.jOutCentral_of_ffOffender_holds hS) h1210
    CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route.k332RowsRest_holds

open CFSG.LocalAnalysis.AGL81TheoremCD in
theorem agl81SectionFifteen_of_cited_inputs_41
    (hK517rt : K517_4b_rank_two_A2B2G2)
    (hvacL : GN15.FFO.PSLNoOffender)
    (hvacU : GN15.FFO.PSUNoOffender)
    (hD4 : GN15.FFOffenderInvertsOddD4)
    (h1210 : Section14.TwelveTenGen) :
    CFSG.Yardstones.Me2c15c2c995a.AGL81SectionFifteen :=
  agl81SectionFifteen_of_theoremDSection15 (agl81TheoremDSection15_of_cited_inputs_41 hK517rt
    hvacL hvacU hD4 h1210)

end CitedInputs41

end CFSG.LocalAnalysis.RankThreeUC.S15
