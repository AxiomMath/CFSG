module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432ClsSpor
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieForkDefs
public import Certificates.Certificate1952
public import Certificates.Certificate2012
public import Certificates.Certificate2266
public import Certificates.Certificate5133
public import Certificates.Certificate8032
public import Certificates.Certificate8064
public import Certificates.Certificate8080
public import Certificates.Certificate8081
public import Certificates.Certificate8117
public import Certificates.Certificate10050
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import Certificates.Certificate18000
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieRed
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieOutProof
import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
import CFSG.LocalAnalysis.GLTheoremA.CatC.LieComp3
import CFSG.LocalAnalysis.GLTheoremA.CatC.LieCompHolds
import CFSG.LocalAnalysis.GLTheoremA.CatA.H1429Inner
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvExcShape
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeALocalBase
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeL1Orb
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMDownMGmat
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporBMInvB
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporBMInvM
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZMathHS5
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420Norm
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434O8pE9Local
public import Certificates.Data.U62Rank.Check

public section


namespace CFSG.LocalAnalysis.GLTheoremA.H1420

theorem i1432ClsD4_of_fork
    (hF : LieOuterThree) : I1432ClsD4 :=
  ClsRed.i1432ClsD4_of_lie <| i1432ClsD4Lie_of_out
    CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
    (kdChevDownQ_three_of_lieComp lieComp_holds) h1429_kdChevInner_three
    (i1432LieOut_of_fork CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
      CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput hF)

theorem i1432ClsG2_of_fork
    (hF : LieOuterThree) : I1432ClsG2 :=
  ClsRed.i1432ClsG2_of_lie <| i1432ClsG2Lie_of_out
    CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
    (kdChevDownQ_three_of_lieComp lieComp_holds) h1429_kdChevInner_three
    (i1432LieOut_of_fork CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
      CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput hF)

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
