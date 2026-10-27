module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOPSUReduction
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.ScalarCore
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

theorem psuNoOffender_holds :
    FFO.PSUNoOffender :=
  fun _ _ _ hm hr hr2 hrmq => psuNoOffenderAt_of_scalar_core hm hr hr2 hrmq
    fun hm5 _ _ _ hV _ hirr _ _ _ _ hK φ hφs hφk _ hc hco _ hAL hA1 hAel hAq hAV =>
      HardMathSupport.Meierfrankenfeld.PSUScalar.scalar_core_ne_one hr hr2
        (hrmq.trans (Nat.gcd_dvd_left _ _)) hm5 hV hirr hK φ hφs hφk hc hco hAL hA1 hAel hAq hAV

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
