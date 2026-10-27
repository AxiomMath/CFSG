module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291R3ExMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292LinUniMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.YSDeltaKData
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291LinUniMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesDeltaMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesNSNotDelta
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesNSSimple

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Yardstones.Md8ed6d263d89 (YSPEmptyPlaneLocals YSPEmptyStrongOfPlaneLocals)

section YS08




theorem ysPEmptyPlaneLocals_of_l6leaves (h0 : KD291LinUniZero) (hM : KD291LinUniModel)
    (hAL : KD292CaseALin) (hAU : KD292CaseAUni) (hBS : KD292CaseBSylow)
    (hBC : KD292CaseBConstr) (hKD : KD291a3) (hRank3 : KFactP65RankThree)
    (hRank2 : KFactP65RankTwo) (hNPC : KFact64iiNPC) (hC : StepKGroupCore) :
    YSPEmptyPlaneLocals :=
  ysPEmptyPlaneLocals_of_delta (kd292LinUni_of_kdata h0 hM hAL hAU hBS hBC) kdR3Exclusion_holds
      (s622DeltaNPC_of_kd291a3 hKD) hRank3 hRank2 (stepNotDeltaOmega_of_kfact64ii hNPC) hC

end YS08

section YS09



theorem ysPEmptyStrongOfPlaneLocals_of_l6leaves (h309 : I291P65.KD309) (hKD : KD291a3)
    (hRank3 : KFactP65RankThree) (hRank2 : KFactP65RankTwo) (h630 : S62L630Iii)
    (hD : S622KFactD) (hKx : S622Kx) : YSPEmptyStrongOfPlaneLocals :=
  ysPEmptyStrongOfPlaneLocals_of_delta I291P65.kd29LinUni_holds h309 (s622DeltaNPC_of_kd291a3 hKD)
      hRank3 hRank2 h630 hD s622KFactSimple_holds hKx

end YS09

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
