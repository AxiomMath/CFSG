module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ThFive
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ThreeKill
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Faithful
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR1Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2Layer
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Alt
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
public import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43Rest
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec3Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.RankThree.Native.ONSevenDefs
public import CFSG.RankThree.Native.ONSevenRestrict
public import CFSG.RankThree.PartOne.SPOR.OuterSimple
public import CFSG.Sporadic.SuzOddCore.GraphData
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import Certificates.Certificate16041
public import Certificates.Certificate2098
public import Certificates.Certificate2103
public import Certificates.Certificate2108
public import Certificates.Certificate2109
public import Certificates.Certificate2274
public import Certificates.Certificate8137
public import Certificates.Certificate8138
public import Certificates.Certificate8139
public import Certificates.Certificate8140
public import Certificates.Certificate8141
public import Certificates.Certificate8145
public import Certificates.Certificate8146

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Sporadic.Th CFSG.Sporadic.SmallOddCore CFSG.EvenSporadicStandard.Solomon78
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.Blueprint CFSG.RankThree.PartTwo.Sec4

theorem sporPlaneKill_Th_five
    (hOut : SporadicOuterLeTwo) : SporPlaneKill .Th 5 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
  have b₀ : NativeSporadic.Carrier .Th ≃* Spor .Th := b
  have bX : ↥JT ≃* Spor .Th := thJTEquiv.symm.trans b₀
  have h0 : ¬ SporadicOnePair .Th 5 := by decide
  have hoff := offPair_Th
  refine @sporPlaneKill_of_noSig_model hOut .Th 5 (by norm_num) (by norm_num) h0 ↥JT
    (Subgroup.toGroup JT) bX ?_ (NativeSporadic.Carrier .Th) _ b₀ hoff
  intro R Y hR hR9 hY3 hRY
  exact th5_noSig R hR hR9 Y ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hY3) hRY

theorem sporPair_Th_five
    (hOut : SporadicOuterLeTwo) : SporPair .Th 5 :=
  sporPair_of_planeKill (sporPlaneKill_Th_five hOut)

end CFSG.HardMathSupport.Dickson.I271
