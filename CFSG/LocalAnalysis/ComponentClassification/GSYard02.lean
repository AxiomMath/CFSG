module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard02CoverLow
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02CoverSz8
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02CoverM12
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02G2
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02Ree
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02PSp4
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02SmallEven
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02Alt
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02J1
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02M12
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02M22
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02M23
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02Ly
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02J2J3
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02McL
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02L5U5
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02D4
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02L4U4
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02CoverL4U4
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02CoverAlt
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2Edge
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL4
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL4Cases
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL4Kill
public import CFSG.GH74.GLS.TwoThin.G.Section
public import CFSG.GH74.GLS.TwoThin.KGroupCore
public import CFSG.GH74.Generic.S1.LinFull
public import CFSG.GH74.KGroups.L28Tables
public import CFSG.GH74.KGroups.L34Aut
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUGraphCore
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUGraphDescent
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUInnerPaired
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModels
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverExternal
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphSymm
public import CFSG.Sporadic.Recognition.McLASSpec
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.Schreier.M23
public import CFSG.Sporadic.Schreier.PairJ3Order
public import CFSG.Walter.J1Recog
public import Certificates.Certificate5007
public import Certificates.Certificate9300

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02

theorem quasisimpleSylowFourJoinedSCN_holds :
    QuasisimpleSylowFourJoinedSCN :=
  quasisimpleSylowFourJoinedSCN_of_cases
    (simpleCase_of_leaves leafG2_holds leafD4_holds leafPSp4_holds leafRee_holds leafL4_holds
      leafU4_holds leafL5_holds leafU5_holds leafSmallEven_holds leafAlt_holds leafM12_holds
      leafM22_holds leafM23_holds leafJ1_holds leafJ2_holds leafJ3_holds leafMcL_holds
      (leafLy_of_coverAlt coverLeafAlt_holds))
    (coverCase_of_low_gh coverLow_holds
      (coverGH_of_leaves coverLeafL4_holds coverLeafU4_holds coverLeafSz8_holds coverLeafAlt_holds
        coverLeafM12_holds))

end CFSG.ComponentClassification.Sol76.Sig.GSYard02
