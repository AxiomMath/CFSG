module

public import CFSG.Yardstones.M9cbf837c48cf.Definitions
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.CyclicOuterAssembly
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionFinal
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTwoGroupAssembly
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialCases
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureFinal
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleSplit
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.ZJAssembly

import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.L34Borel
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.L34Graph
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.L34Unitary
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.U3Involution
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialFamilies
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialAlt
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialSporadicTits
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialSporadicMcL
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialSporadicJ4

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth

open CFSG.LocalAnalysis.RankThreeTheoremC

section Assembly

theorem gl83GenericKFacts_of_open (hS : CyclicOuter.SeitzOuterRankOne)
    (hWC : WeakClosure.CrossCharTagsRest) (hCP : KFactComponentPCoreThree) (hBal : Bal3KFacts)
    (hA : AlmostSimple.AlmostSimplePartA) (hB2 : AlmostSimple.AlmostSimplePartBRankTwo) :
    CFSG.Yardstones.M9cbf837c48cf.GL83GenericKFactsStatement :=
  ⟨CyclicOuter.stronglyEmbeddedCyclicOuter_of_seitzRankOne hS,
    TwoSignalizer.signalizerTwoGroupKFact_holds,
    SignalizerTrivial.kFactSignalizerTrivial_of_cases SignalizerTrivial.signalizerTrivialL2_holds
        SignalizerTrivial.signalizerTrivialU3_holds SignalizerTrivial.signalizerTrivialAlt_holds
        SignalizerTrivial.signalizerTrivialTits_holds SignalizerTrivial.signalizerTrivialMcL_holds
        SignalizerTrivial.signalizerTrivialJ4_holds,
    WeakClosure.kFactWeakClosure_of_tagsRest hWC,
    InnerAction.kFactInnerAction_holds, kFactU3Involution, hCP, kFactL34Unitary, kFactL34Borel,
    kFactL34Graph, hBal, ZJ.kFactZJFactorization_holds,
    AlmostSimple.kFactAlmostSimpleRankTwo_of_parts hA (AlmostSimple.almostSimplePartB_of_rankTwo hB2)⟩

end Assembly

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth
