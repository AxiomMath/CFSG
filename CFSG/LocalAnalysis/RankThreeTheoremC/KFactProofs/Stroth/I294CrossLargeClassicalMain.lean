module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossLargeClassical
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossLargeLinear
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossLargeUni
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossLargeSp
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossLargeOmMain

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

theorem i294LargeModelPSL_holds : I294LargeModelPSL :=
  fun _ hr h5 _ _ _ hrK _ hLU hS => I294Large.rank_psl hr h5 hrK hLU hS

theorem i294CrossLargePrimeOn_classical_holds : I294CrossLargePrimeOn I294CrossIsClassical :=
  i294CrossLargePrimeOn_classical_of_models i294LargeModelPSL_holds i294LargeModelPSU_holds
    i294LargeModelPSp_holds i294LargeModelPOmegaOdd_holds i294LargeModelPOmegaPlus_holds
    i294LargeModelPOmegaMinus_holds

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
