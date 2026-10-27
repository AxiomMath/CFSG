module

public import CFSG.HardMathSupport.Curtis.Coordinator.ExcLeafDefs
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNSylow
public import CFSG.HardMathSupport.Foote.E27.SporSylowBound
public import CFSG.HardMathSupport.Foote.E27.SporKill
public import CFSG.LieType.SeitzGeneration.ExcPlaneModel
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellUniOuter
public import CFSG.HardMathSupport.Curtis.Proving.ToralCaseSplit
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Reduction
public import CFSG.HardMathSupport.Timmesfeld.LinearRank.LinCover
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Linear
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.Chevalley.SignKernelComponentPerfect
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLHatAssembly
public import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.Census3.Assembly
public import CFSG.RankThree.PartOne.FOC.Assemble
public import CFSG.RankThree.PartOne.FOC.CentralQuot
public import CFSG.RankThree.PartOne.FOC.ListBridge
public import CFSG.RankThree.PartOne.FOC.PSUModel
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizer
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon
public import CFSG.RankThree.PartOne.S11d.LayerDecomp
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartTwo.Census.Spin.Main
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate8153
public import Certificates.Certificate8156
public import Certificates.Certificate8157
public import Certificates.Certificate8160
public import Certificates.Certificate8171

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType
  CFSG.TauCetiBridge CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Foote.E27 TauCeti
open CFSG.HardMathSupport.Malle.E27Lie (InnerLeaf)

open CFSG.HardMathSupport.Curtis.Coordinator.ExcLeaf (IdxExc)


section Certs


theorem innerLeaf_E7_two : InnerLeaf (IdxExc .E7 2) := by
  intro X _ _ K R T z h hz d hd e
  obtain ⟨i, hv⟩ := d
  obtain ⟨q, hq, hr, rfl⟩ := hd
  obtain ⟨ψ⟩ := e
  obtain ⟨F, _, _, hF, -, ⟨ε⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  have h3 : 3 ∣ Nat.card F + 1 := by rw [hF]; omega
  obtain ⟨P, hP, hprop⟩ := exists_kill_subgroup_E78_neg (τ := Tag.E7) (Or.inl rfl) h3
  obtain ⟨S₀⟩ : Nonempty (Sylow 3 ↥K) := inferInstance
  refine h.false_of_sylow_kill hz S₀ fun s hs hs3 => Or.inl ?_
  exact dvd81_card_sylow_inf_centralizer_of_equiv (ψ.trans ε) P hP hprop S₀ hs hs3

theorem innerLeaf_E8_two : InnerLeaf (IdxExc .E8 2) := by
  intro X _ _ K R T z h hz d hd e
  obtain ⟨i, hv⟩ := d
  obtain ⟨q, hq, hr, rfl⟩ := hd
  obtain ⟨ψ⟩ := e
  obtain ⟨F, _, _, hF, -, ⟨ε⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have h3 : 3 ∣ Nat.card F + 1 := by rw [hF]; omega
  obtain ⟨P, hP, hprop⟩ := exists_kill_subgroup_E78_neg (τ := Tag.E8) (Or.inr rfl) h3
  obtain ⟨S₀⟩ : Nonempty (Sylow 3 ↥K) := inferInstance
  refine h.false_of_sylow_kill hz S₀ fun s hs hs3 => Or.inl ?_
  exact dvd81_card_sylow_inf_centralizer_of_equiv (ψ.trans ε) P hP hprop S₀ hs hs3

end Certs

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

end
