module

public import CFSG.HardMathSupport.Curtis.Coordinator.ExcLeafDefs
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.CubeCentralizer
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.E78Sylow
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.E78Torsion
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


theorem exists_kill_subgroup_E78 {τ : Tag} (hτ : τ = Tag.E7 ∨ τ = Tag.E8) {F : Type} [Field F]
    [Finite F] (h3 : 3 ∣ Nat.card F - 1) :
    ∃ P : Subgroup ↥(adjointGroup τ F),
      Nat.card P = 3 ^ (Nat.card ↥(adjointGroup τ F)).factorization 3 ∧
      ∀ w ∈ P, orderOf w = 3 →
        81 ∣ Nat.card ↥(P ⊓ Subgroup.centralizer ({w} : Set ↥(adjointGroup τ F))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite ↥(adjointGroup τ F) := generated_group_finite τ F
  obtain ⟨P, hPN⟩ : ∃ P : Sylow 3 ↥(adjointGroup τ F),
      (P : Subgroup ↥(adjointGroup τ F)) ≤ monomialSub τ F := by
    rcases hτ with rfl | rfl
    · exact exists_sylow_three_le_monomialSub_E7 F h3
    · exact exists_sylow_three_le_monomialSub_E8 F h3
  refine ⟨P, Sylow.card_eq_multiplicity P, ?_⟩
  intro w hwP hw3
  have hV3 := torusPow_three_pow_eq_one (τ := τ) (K := F)
  have hVc := torusPow_mul_comm (τ := τ) (K := F)
  have hPnorm : ∀ p ∈ (P : Subgroup ↥(adjointGroup τ F)), ∀ v ∈ TableBExc.torusPow τ F 3,
      p * v * p⁻¹ ∈ TableBExc.torusPow τ F 3 :=
    fun p hp v hv => torusPow_normalized p (hPN hp) v hv
  have hVp : IsPGroup 3 (TableBExc.torusPow τ F 3) := fun v => ⟨1, by
    simpa using Subtype.ext (hV3 v v.2)⟩
  have hnorm : (P : Subgroup ↥(adjointGroup τ F)) ≤
      Subgroup.normalizer (TableBExc.torusPow τ F 3 : Set ↥(adjointGroup τ F)) := by
    intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro v
    refine ⟨fun hv => hPnorm p hp v hv, fun hv => ?_⟩
    have := hPnorm p⁻¹ (inv_mem hp) _ hv
    rwa [show p⁻¹ * (p * v * p⁻¹) * p⁻¹⁻¹ = v by group] at this
  have hVP : TableBExc.torusPow τ F 3 ≤ (P : Subgroup ↥(adjointGroup τ F)) := by
    have hsup := hVp.to_sup_of_normal_left' P.isPGroup' hnorm
    exact le_sup_left.trans (le_of_eq (P.3 hsup le_sup_right))
  have hw1 : w ^ 3 = 1 := by
    have h := pow_orderOf_eq_one w
    rwa [hw3] at h
  have hr : 7 ≤ τ.rank := by rcases hτ with rfl | rfl <;> decide
  have hcard : 3 ^ 7 ≤ Nat.card (TableBExc.torusPow τ F 3) :=
    (Nat.pow_le_pow_right (by norm_num) hr).trans (three_pow_rank_le_card_torusPow hτ h3)
  exact dvd81_card_inf_centralizer_of_cube P.isPGroup' hVP hPnorm hVc hV3 hcard hwP hw1

theorem innerLeaf_E7_one : InnerLeaf (IdxExc .E7 1) := by
  intro X _ _ K R T z h hz d hd e
  obtain ⟨i, hv⟩ := d
  obtain ⟨q, hq, hr, rfl⟩ := hd
  obtain ⟨ψ⟩ := e
  obtain ⟨F, _, _, hF, -, ⟨ε⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  have h3 : 3 ∣ Nat.card F - 1 := by rw [hF]; omega
  obtain ⟨P, hP, hprop⟩ := exists_kill_subgroup_E78 (τ := Tag.E7) (Or.inl rfl) h3
  obtain ⟨S₀⟩ : Nonempty (Sylow 3 ↥K) := inferInstance
  refine h.false_of_sylow_kill hz S₀ fun s hs hs3 => Or.inl ?_
  exact dvd81_card_sylow_inf_centralizer_of_equiv (ψ.trans ε) P hP hprop S₀ hs hs3

theorem innerLeaf_E8_one : InnerLeaf (IdxExc .E8 1) := by
  intro X _ _ K R T z h hz d hd e
  obtain ⟨i, hv⟩ := d
  obtain ⟨q, hq, hr, rfl⟩ := hd
  obtain ⟨ψ⟩ := e
  obtain ⟨F, _, _, hF, -, ⟨ε⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have h3 : 3 ∣ Nat.card F - 1 := by rw [hF]; omega
  obtain ⟨P, hP, hprop⟩ := exists_kill_subgroup_E78 (τ := Tag.E8) (Or.inr rfl) h3
  obtain ⟨S₀⟩ : Nonempty (Sylow 3 ↥K) := inferInstance
  refine h.false_of_sylow_kill hz S₀ fun s hs hs3 => Or.inl ?_
  exact dvd81_card_sylow_inf_centralizer_of_equiv (ψ.trans ε) P hP hprop S₀ hs hs3

end Certs

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

end
