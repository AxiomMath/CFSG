module

public import CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.E6ThreeAssembly
public import CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.E7Six
public import CFSG.HardMathSupport.Lang.TwE6Step3.Assembly
public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.Assembly
public import CFSG.LieType.SeitzGeneration.HyperExCubeLevi
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Fixed
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2A2Case
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
public import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
public import CFSG.RankThree.Lattice.SteinbergBIGenPerfect
public import CFSG.RankThree.Lattice.SteinbergBIGenQuasisimple
public import CFSG.RankThree.PartOne.KE.Basic
public import CFSG.RankThree.PartOne.KE.E6FourData
public import CFSG.RankThree.PartOne.KE.E8FiveData
public import CFSG.RankThree.PartOne.KE.E8NineData
public import CFSG.RankThree.PartOne.KE.NativeCyclicMain
public import CFSG.RankThree.PartOne.KE.PlaneToral
public import CFSG.RankThree.PartOne.KE6.Phi6Decomp
public import CFSG.RankThree.PartOne.KE6.Phi6Excl
public import CFSG.RankThree.PartOne.KE6.Phi6Frame
public import CFSG.RankThree.PartOne.KF4.KernelTools
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.AnisoCube

theorem excCubeResidualsV4_of_frontiers
    (h6 : E6ThreeD4Lines)
    (hTw : CFSG.HardMathSupport.Lang.TwE6Step3.TwE6SixLines)
    (h7 : CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.E7SixStep3Adj) :
    CFSG.LieType.SeitzGeneration.ExcCubeResidualsV4 :=
  ⟨excCubeHighAt_E6_three_of_d4Lines h6,
    excCubeHighAt_E7_six_of_plane
      (CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.e7SixPlane_of_step3Adj h7),
    CFSG.HardMathSupport.Lang.TwE6Step3.excCubeHighAt_twistedE6_six_of_lines hTw⟩

end CFSG.HardMathSupport.Foote.Coordinator.AnisoCube

end
