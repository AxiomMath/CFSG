module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.FusionSylow
public import CFSG.Sporadic.SmallOddCore.HSLocal
public import CFSG.Sporadic.Schreier.PairHSOrder
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.HSInvolutions
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UHSFacts
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.WpGTypes
import Certificates.Kernel.Sporadic.HS.L2273F
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.Statements
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdFamilies
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoDefs
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoJ
public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootConj
public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootPartner
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapTable
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTwoMain
public import CFSG.LocalAnalysis.OddStandard.Solomon75Goldschmidt
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Reduce
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5Base
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5DefsModel
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.PairTypes
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdInputs3
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatSporadicSix
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatSporadicSix
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34HS
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCatOmegaMinusSporadic
public import CFSG.Milestones.SG_two_signalizer_completeness
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.Sporadic.Bridge.BOrder
public import CFSG.Sporadic.Bridge.BSurjInputs
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.HN.CertificateBase
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.ON.SimpleBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.Th.CertificateBase
public import CFSG.Sporadic.Th.CertificateBase1
public import CFSG.Sporadic.ThSchreier.KernelAutBase
public import CFSG.Sporadic.ThSchreier.KernelAutBase1
public import CFSG.StronglyEmbedded.TheoremSE.BenderLowRank
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount
public import CFSG.Walter.JRFacts
public import Certificates.Certificate10027
public import Certificates.Certificate10095
public import Certificates.Certificate10095Base
public import Certificates.Certificate10100
public import Certificates.Certificate10101
public import Certificates.Certificate10102
public import Certificates.Certificate10104
public import Certificates.Certificate10107
public import Certificates.Certificate10108
public import Certificates.Certificate10110
public import Certificates.Certificate10111
public import Certificates.Certificate2130
public import Certificates.Certificate2135
public import Certificates.Certificate2136
public import Certificates.Certificate2139
public import Certificates.Certificate2140
public import Certificates.Certificate2145
public import Certificates.Certificate2323
public import Certificates.Certificate3085Base
public import Certificates.Certificate9201

public section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four CFSG.PSL3Four.Native
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier
open Subgroup

theorem hsT2_mem_ord :
    hsT2 ∈ hsP ∧ orderOf hsT2 = 2 := by
  obtain ⟨-, -, -, hrows, -⟩ := hs_involution_centralizers
  obtain ⟨-, h2, hout, -⟩ := hrows _ (List.mem_cons_of_mem _ List.mem_cons_self)
  dsimp only at h2 hout
  refine ⟨?_, h2⟩
  by_contra h
  exact Bool.false_ne_true (hout.2 h)

end CFSG.Sporadic.SmallOddCore

