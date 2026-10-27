module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWInvolutionU
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWUnitaryLines
public import CFSG.GH74.GLS.SP.Local.SPLRestrict
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Phi36Plane
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.Cover
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.FamilyProved
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.ThreeQ1
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.ClosingOddProved
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.OuterThree
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.Phi6RouteW
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWSylow
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.SeitzGeneration.ExcOuterTriality
public import CFSG.LieType.SeitzGeneration.OrthLift
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAlignCores
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7Split
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseLTorus
public import CFSG.RankThree.PartOne.SEITZ6.G2MaxDone
public import Certificates.Kernel.SporSch.Th.Plane2320

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.K1214
  CFSG.RankThree.PartOne.K128 CFSG.GH74.GLS.Stage2.Bender.Thm1

local notation "𝒞[" K ", " σ "]" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
