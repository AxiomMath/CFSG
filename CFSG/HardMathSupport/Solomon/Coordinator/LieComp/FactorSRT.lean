module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTGeneric
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSL
public import Certificates.Certificate113
import CFSG.LieType.Ree.SuzukiPerfect
import CFSG.LieType.Ree.SuzukiSimple
import CFSG.RankThree.PartTwo.Sec4.Census.BridgeSuzuki
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport
import CFSG.StronglyEmbedded.Catalog.Suzuki
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.Monster.GMS.Fi23Gen
public import CFSG.Monster.GMS.Fi23GenIso
public import CFSG.Monster.GMS.Fi23GenSix
public import CFSG.Monster.GMS.LeechCoh
public import CFSG.Monster.GMS.LeechCohGroup
public import CFSG.Monster.GMS.S365Center
public import CFSG.Monster.GMS.S37
public import CFSG.Monster.GMS.S4Assembly
public import CFSG.Monster.GMS.S4CohB
public import CFSG.Monster.GMS.S5Inputs
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.KC.LinearCommutantFactors
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.Sporadic.Co1.Module.Co2Stab
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.M24
public import CFSG.Sporadic.SuzOddCore.GraphData
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate16005
public import Certificates.Certificate16041
public import Certificates.Certificate2
public import Certificates.Certificate2098
public import Certificates.Certificate2103
public import Certificates.Certificate2108
public import Certificates.Certificate2109
public import Certificates.Certificate2139
public import Certificates.Certificate2140
public import Certificates.Certificate2274
public import Certificates.Certificate2323
public import Certificates.Certificate3
public import Certificates.Certificate3044
public import Certificates.Certificate3122
public import Certificates.Certificate3123
public import Certificates.Certificate3130
public import Certificates.Certificate3133
public import Certificates.Certificate3134
public import Certificates.Certificate3136
public import Certificates.Certificate3137
public import Certificates.Certificate3176
public import Certificates.Certificate3179
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate8
public import Certificates.Certificate8046
public import Certificates.Certificate8049
public import Certificates.Certificate8052
public import Certificates.Certificate9
public import Certificates.Certificate9124
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.Blueprint CFSG.LieType.Ree

theorem suzuki_valid {b : ℕ} (hb : 1 ≤ b) : (TauCeti.LieTypeIndex.suzuki b).Valid := by
  rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
  exact ⟨hb, fun h => h⟩

theorem nonempty_suzukiGroup_equiv_cat {b : ℕ} (hb : 1 ≤ b) {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 2 ^ (2 * b + 1)) :
    Nonempty (suzukiGroup b k ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki b, suzuki_valid hb⟩).Group) :=
  ⟨(CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hk).trans
    (CFSG.BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup (suzuki_valid hb)).symm⟩

theorem isChevSimple_suzukiGroup {b : ℕ} (hb : 1 ≤ b) {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 2 ^ (2 * b + 1)) :
    CFSG.Yardstones.Md0ec50421ce4.IsChevSimple 2 (suzukiGroup b k) :=
  Or.inl ⟨.lie ⟨.suzuki b, suzuki_valid hb⟩, TauCeti.LieTypeIndex.characteristic_suzuki b,
    nonempty_suzukiGroup_equiv_cat hb hk⟩

theorem suzukiGroup_simple_nonab {b : ℕ} (hb : 1 ≤ b) {k : Type}
    [Field k] [Finite k] (hk : Nat.card k = 2 ^ (2 * b + 1)) :
    Finite (suzukiGroup b k) ∧ IsSimpleGroup (suzukiGroup b k) ∧
      ∃ x y : suzukiGroup b k, x * y ≠ y * x := by
  obtain ⟨hfin, hnt, hsimple⟩ := suzuki_simple hb hk
  have hperf : Group.IsPerfect (suzukiGroup b k) := (suzuki_perfect hb hk).2
  refine ⟨hfin, hsimple, ?_⟩
  by_contra hcon
  push Not at hcon
  exact Group.IsPerfect.not_isMulCommutative (suzukiGroup b k) ⟨⟨hcon⟩⟩

theorem lieFactorData_suzukiGroup {b : ℕ} (hb : 1 ≤ b) {k : Type}
    [Field k] [Finite k] (hk : Nat.card k = 2 ^ (2 * b + 1)) :
    LieFactorData 2 (suzukiGroup b k) := by
  obtain ⟨hfin, hs, hnc⟩ := suzukiGroup_simple_nonab hb hk
  haveI := hfin
  haveI := hs
  exact LieFactorData.of_simple hnc (isChevSimple_suzukiGroup hb hk)

theorem lieFactorData_SL2 {K : Type} [Field K] [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K) :
    LieFactorData 2 (Matrix.SpecialLinearGroup (Fin 2) K) := by
  haveI := Fintype.ofFinite K
  have h := slFactorFacts_holds K 2 le_rfl (fun _ => by rw [← Nat.card_eq_fintype_card]; exact h4)
  rwa [ringChar.eq K 2] at h

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
