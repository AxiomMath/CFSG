module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K5192P2
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNInputRed
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15P2GlueAtM
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoHolds
import CFSG.LocalAnalysis.RankThreeUC.GN15Holds
import CFSG.LocalAnalysis.RankThreeUC.GN15SolvAlt

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.GN CFSG.Quasithin
  CFSG.AGLEmbedding CFSG.Open


theorem k5192P2_holds
    : K5192P2 :=
  k5192P2_of_atM fun X _ _ T hgn hne halt T₁ T₂ hc =>
    ⟨GN15.gnFactor_of_absorbs_H_of_outer_commutative hgn hc (GN15.gnAbsorbs_H_holds hgn hc)
      fun L hL _ => by
        obtain ⟨e⟩ := halt L hL
        obtain ⟨-, ⟨e'⟩⟩ := center_eq_bot_and_quotient_of_mulEquiv_alternatingGroup (by norm_num) e
        exact GN15.isMulCommutative_outer_of_isComponentOf_alternating hL (le_refl 5) e',
      GNInputRed.gnShape_of_residuals
        CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.ffModuleTheorem_holds
        (gnAltFacts_of_gf2EightFive
          (CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.gf2EightFive_of_b42L42Core
            CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.b42L42Core_holds)
          (gnAltRest_of_seven (gnAltRestSeven_of_threeRank
            CFSG.AGLEmbeddingD2.McLaughlin.A7Six.gnAltSevenThreeRank_proved)))
        GNInputRed.rankTwo_holds GN15.altEven_holds hgn hne hc⟩

end CFSG.LocalAnalysis.RankThreeUC.S15

end
