module

public import CFSG.ClassicalInvolution.WeakCT.TwistedSpinModel
public import CFSG.ClassicalInvolution.WeakCT.Blocks
import CFSG.Open.StatedDefs
import CFSG.RankThree.PartOne.CTP.SpinMinusEven
import CFSG.ClassicalInvolution.WeakCT.SpCharts
import CFSG.ClassicalInvolution.WeakCT.Standard
import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCPairs
import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCRecognition
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaMinus
public import CFSG.CharacterTheory.Semidihedral.ElementStructure
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.ClassicalInvolution.WeakCT.SpinMinus
public import CFSG.LieType.TitsSimplicity
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.CGT.Timmesfeld75.ListWCBasic
import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
import CFSG.ClassicalGroups
import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLevi
import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
import CFSG.ClassicalInvolution.QuaternionStructure
import CFSG.Fischer.Uniq.CompTau
import CFSG.Foundations
import CFSG.GH74.GLS.Defs
import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
import CFSG.GH74.GLS.Stage2.Final.LayerFDerive
import CFSG.GH74.Statements
import CFSG.LieType.Chevalley.C2E6StandardFixedData
import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
import CFSG.LieType.CurtisTits.Adjoint
import CFSG.LieType.Ree.LargeReeEightTorus
import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenE6
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
import CFSG.LocalAnalysis.ComponentClassification.KProper
import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelCases
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.LocalAnalysis.SectionRank.TitsCover
import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp
import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeAutMain
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotBLiftAniso
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatCovers
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotGlobal
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR7iii
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotLeviFactFour
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSetup
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaNeighbour
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotParamMain
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeFieldFour
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRowsTables
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeModel
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotAlignImagesSwap
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
import CFSG.Quasithin.Background.A1cTransfer
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.A3ComponentsAmbient
import CFSG.Quasithin.Background.G11Stmts
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.AUTSL.OmegaFamily
import CFSG.RankThree.PartOne.AUTSL.Rows
import CFSG.RankThree.PartOne.AUTSL.SylowTrick
import CFSG.RankThree.PartOne.CTP.StrongPSylow
import CFSG.RankThree.PartOne.KC.OrthogonalHighWittFixedSpace
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSetting
import CFSG.RankThree.PartOne.KC.UnitaryLiftBlocks
import CFSG.RankThree.PartOne.KF.UnitaryModel
import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.RankThree.PartOne.S12.Sec1511Y1
import CFSG.RankThree.PartOne.S12.Sec15Items
import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary
import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
import CFSG.Sporadic.Bridge.LyData
import CFSG.Sporadic.Fi24.Faithful
import CFSG.Sporadic.Fi24.SepSpec
import CFSG.Sporadic.HN.CertificateBase
import CFSG.Sporadic.J4Base
import CFSG.Sporadic.Ly.ActionBase
import CFSG.Sporadic.Ly.CertificateBase
import CFSG.Sporadic.Ly.FaithSpec
import CFSG.Sporadic.Ly.OrbitSpec
import CFSG.Sporadic.Ly.Simple
import CFSG.Sporadic.LyBase
import CFSG.Sporadic.ON.SimpleBase
import CFSG.Sporadic.Presentation.Ly
import CFSG.Sporadic.Schreier.LyChain11
import CFSG.Sporadic.Schreier.TitsOther
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
import CFSG.Walter.JRFacts
import Certificates.Certificate10
import Certificates.Certificate1016Base
import Certificates.Certificate1021
import Certificates.Certificate11
import Certificates.Certificate12
import Certificates.Certificate3
import Certificates.Certificate3085Base
import Certificates.Certificate4
import Certificates.Certificate42
import Certificates.Certificate44
import Certificates.Certificate5
import Certificates.Certificate6
import Certificates.Certificate7
import Certificates.Certificate8
import Certificates.Certificate9

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras
  CFSG.ClassicalInvolution.Models.TwistedPairs
open scoped MatrixGroups


theorem twistedB2BlockStandardPair_minusDatum_even {F : Type} [Field F] [Finite F] [CharP F 2]
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ} (hn : 4 ≤ n) {i j : Fin (n - 1)}
    (hia : i.val + 3 = n) (hjb : j.val + 2 = n) :
    ∃ W, TwistedB2BlockStandardPair hirr W (CurtisTits.rankOne (minusDatum n hirr).rootGroup i)
      (CurtisTits.rankOne (minusDatum n hirr).rootGroup j) := by
  have := fact_shortField hirr
  have hn3 : 3 ≤ n := by omega
  have hi : i.val + 1 < n - 1 := by omega
  have hj : ¬ j.val + 1 < n - 1 := by omega
  have hinj := CFSG.RankThree.PartOne.CTP.spinGroupMap_minusShift_injective_even n hn3 hirr
  have hl := minusShift_comp_longBlock (b := b) (c := c) hn3 hia hi
  have hs := minusShift_comp_shortBlock hn3 hirr hjb
  refine ⟨((minusShift n hn3 b c).spinGroupMap).range, (minusShift n hn3 b c).spinGroupMap, rfl,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [(MonoidHom.ker_eq_bot_iff _).mpr hinj]
    exact bot_le
  · change Function.Injective ((minusShift n hn3 b c).spinGroupMap.comp (minusLongBlock b c))
    rw [hl]
    exact rLong_injective hi
  · change Function.Injective
      ((minusShift n hn3 b c).spinGroupMap.comp (shortBlock hirr 3 finOne))
    rw [hs]
    exact CFSG.RankThree.PartOne.CTP.shortBlock_injective_even hirr n j
  · change (minusLongBlock b c).range.map (minusShift n hn3 b c).spinGroupMap = _
    rw [← MonoidHom.range_comp, hl, rankOne_minusDatum_long hirr hi]
  · change (shortBlock hirr 3 finOne).range.map (minusShift n hn3 b c).spinGroupMap = _
    rw [← MonoidHom.range_comp, hs, rankOne_minusDatum_short hirr hj]

private theorem omc_comm {r : ℕ} {F : Type} [Field F] [Finite F] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {G : Type} [Group G]
    (σ : SL(r + 2, F) →* G) (κ : spinGroup (quadMinus (r + 2) F b c) →* G)
    (hagree : ∀ k : Fin r, (σ.comp (blockSL2 F (r + 1) k.succ)).range =
      (CurtisTits.rankOne (minusDatum (r + 2) hirr).rootGroup k.castSucc).map κ)
    (hcross : ∀ a ∈ (σ.comp (blockSL2 F (r + 1) 0)).range,
      ∀ b ∈ (CurtisTits.rankOne (minusDatum (r + 2) hirr).rootGroup (Fin.last r)).map κ,
        a * b = b * a)
    (U : Fin (r + 2) → Subgroup G)
    (hU : ∀ k : Fin (r + 1), U (Fin.castSucc k) = (σ.comp (blockSL2 F (r + 1) k)).range)
    (hUlast : U (Fin.last (r + 1)) =
      (CurtisTits.rankOne (minusDatum (r + 2) hirr).rootGroup (Fin.last r)).map κ) :
    ∀ i j : Fin (r + 2), i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a := by
  have := fact_shortField hirr
  intro i j hij a ha b hb
  rcases Fin.eq_castSucc_or_eq_last (n := r + 1) i with ⟨i', rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last (n := r + 1) j with ⟨j', rfl⟩ | rfl
    · rw [hU i'] at ha
      rw [hU j'] at hb
      obtain ⟨A, rfl⟩ := MonoidHom.mem_range.mp ha
      obtain ⟨B, rfl⟩ := MonoidHom.mem_range.mp hb
      change σ (blockSL2 F (r + 1) i' A) * σ (blockSL2 F (r + 1) j' B) =
        σ (blockSL2 F (r + 1) j' B) * σ (blockSL2 F (r + 1) i' A)
      rw [← map_mul, ← map_mul,
        blockSL2_comm (K := F) (n := r + 1) i' j' (by simpa using hij) A B]
    · rw [hUlast] at hb
      have hi'lt : (i' : ℕ) < r := by
        have h := hij
        simp only [Fin.val_castSucc, Fin.val_last] at h
        omega
      rcases Nat.eq_zero_or_pos i'.val with h0 | hpos
      · have hi0 : i' = 0 := Fin.ext (by simpa using h0)
        rw [hi0, hU 0] at ha
        exact hcross a ha b hb
      · obtain ⟨k, hk⟩ : ∃ k : Fin r, k.succ = i' :=
          ⟨⟨i'.val - 1, by omega⟩, Fin.ext (by simp only [Fin.val_succ]; omega)⟩
        rw [← hk, hU k.succ, hagree k] at ha
        obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp ha
        obtain ⟨B, hB, rfl⟩ := Subgroup.mem_map.mp hb
        have hki : (k.castSucc : ℕ) + 1 < (Fin.last r : Fin (r + 1)).val := by
          have h := congrArg Fin.val hk
          simp only [Fin.val_succ, Fin.val_last, Fin.val_castSucc] at h ⊢
          omega
        change κ A * κ B = κ B * κ A
        rw [← map_mul, ← map_mul,
          commute_rankOne_minusDatum (n := r + 2) hirr k.castSucc (Fin.last r) hki A hA B hB]
  · exact absurd hij (by have := j.isLt; simp only [Fin.val_last] at hij; omega)

private theorem omc_iSup_le {r : ℕ} {F : Type} [Field F] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {G : Type} [Group G]
    (σ : SL(r + 2, F) →* G) (κ : spinGroup (quadMinus (r + 2) F b c) →* G)
    (U : Fin (r + 2) → Subgroup G)
    (hU : ∀ k : Fin (r + 1), U (Fin.castSucc k) = (σ.comp (blockSL2 F (r + 1) k)).range)
    (hUlast : U (Fin.last (r + 1)) =
      (CurtisTits.rankOne (minusDatum (r + 2) hirr).rootGroup (Fin.last r)).map κ) :
    (⨆ k, U k) ≤ σ.range ⊔ κ.range := by
  refine iSup_le fun k => ?_
  rcases Fin.eq_castSucc_or_eq_last (n := r + 1) k with ⟨k', rfl⟩ | rfl
  · rw [hU k', ← MonoidHom.map_range σ (blockSL2 F (r + 1) k')]
    exact (Subgroup.map_le_range σ _).trans le_sup_left
  · rw [hUlast]
    exact (Subgroup.map_le_range κ _).trans le_sup_right

private theorem omc_le_iSup {r : ℕ} (hr : 2 ≤ r) {F : Type} [Field F] [Finite F] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {G : Type} [Group G]
    (σ : SL(r + 2, F) →* G) (κ : spinGroup (quadMinus (r + 2) F b c) →* G)
    (hagree : ∀ k : Fin r, (σ.comp (blockSL2 F (r + 1) k.succ)).range =
      (CurtisTits.rankOne (minusDatum (r + 2) hirr).rootGroup k.castSucc).map κ)
    (U : Fin (r + 2) → Subgroup G)
    (hU : ∀ k : Fin (r + 1), U (Fin.castSucc k) = (σ.comp (blockSL2 F (r + 1) k)).range)
    (hUlast : U (Fin.last (r + 1)) =
      (CurtisTits.rankOne (minusDatum (r + 2) hirr).rootGroup (Fin.last r)).map κ) :
    σ.range ⊔ κ.range ≤ ⨆ k, U k := by
  refine sup_le ?_ ?_
  · rw [MonoidHom.range_eq_map, ← iSup_range_blockSL2 (K := F) (n := r + 1), Subgroup.map_iSup]
    refine iSup_le fun k => ?_
    rw [MonoidHom.map_range, ← hU k]
    exact le_iSup U (Fin.castSucc k)
  · rw [MonoidHom.range_eq_map,
      ← iSup_rankOne_minusDatum (hirr := hirr) (n := r + 2) (by omega), Subgroup.map_iSup]
    change (⨆ k : Fin (r + 1),
      (CurtisTits.rankOne (minusDatum (r + 2) hirr).rootGroup k).map κ) ≤ ⨆ k, U k
    refine iSup_le fun k => ?_
    by_cases hk : k.val + 1 < r + 1
    · have hk' : k.val < r := by omega
      have hkc : k = (⟨k.val, hk'⟩ : Fin r).castSucc := Fin.ext rfl
      rw [hkc, ← hagree ⟨k.val, hk'⟩, ← hU (⟨k.val, hk'⟩ : Fin r).succ]
      exact le_iSup U (Fin.castSucc (⟨k.val, hk'⟩ : Fin r).succ)
    · have hklt : k.val < r + 1 := k.isLt
      have hkr : k.val = r := by omega
      have hkl : k = Fin.last r := Fin.ext (by simpa using hkr)
      rw [hkl, ← hUlast]
      exact le_iSup U (Fin.last (r + 1))

private theorem omc_recog {n f : ℕ}
    (hadm : CFSG.Open.StatedLieAdmissible .POmegaMinus n 2 f)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ f)
    (hq : 4 ≤ Nat.card F) {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {G : Type} [Group G] (U : Fin (n - 1) → Subgroup G)
    (hcomm : ∀ i j : Fin (n - 1), i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin (n - 1), i.val + 1 = j.val → j.val + 2 < n →
      ∃ W, LinearBlockStandardPair F W (U i) (U j))
    (htw : ∀ i j : Fin (n - 1), i.val + 3 = n → j.val + 2 = n →
      ∃ W, TwistedB2BlockStandardPair hirr W (U i) (U j)) :
    ∃ Ψ : spinGroup (quadMinus n F b c) →* G,
      Ψ.ker ≤ Subgroup.center (spinGroup (quadMinus n F b c)) ∧
      Ψ.range = ⨆ k, U k := by
  let Ks : Subgroup G := ⨆ k, U k
  have hUle : ∀ k, U k ≤ Ks := fun k => le_iSup U k
  obtain ⟨Ψ', hsurj, hker, -⟩ :=
    CFSG.RankThree.PartOne.CTP.weakCT_spinMinus_even hadm hF hq hirr
      (U := fun k => (U k).subgroupOf Ks)
      (CFSG.ClassicalInvolution.Models.SymplecticPairs.iSup_subgroupOf_eq_top U)
      (fun i j hij a ha b hb =>
        Subtype.ext (hcomm i j hij a.1 (Subgroup.mem_subgroupOf.mp ha) b.1
          (Subgroup.mem_subgroupOf.mp hb)))
      (fun i j hij hj => by
        obtain ⟨W, hW⟩ := hpair i j hij hj
        exact ⟨W.subgroupOf Ks,
          CFSG.ClassicalInvolution.Models.SymplecticPairs.linearBlockStandardPair_subgroupOf
            ((CFSG.ClassicalInvolution.Models.SymplecticPairs.linearBlockStandardPair_le_sup
              hW).trans (sup_le (hUle i) (hUle j))) hW⟩)
      (fun i j hi hj => by
        obtain ⟨W, hW⟩ := htw i j hi hj
        exact ⟨W.subgroupOf Ks,
          CFSG.SeitzReduction.SymplecticPilot.kOmega_twistedB2BlockStandardPair_subgroupOf
            ((CFSG.SeitzReduction.SymplecticPilot.kOmega_twistedB2BlockStandardPair_le_sup
              hW).trans (sup_le (hUle i) (hUle j))) hW⟩)
  refine ⟨Ks.subtype.comp Ψ', ?_, ?_⟩
  · intro x hx
    exact hker (Subtype.ext (MonoidHom.mem_ker.mp hx))
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]

private theorem omc_tw {r : ℕ} (hr : 2 ≤ r) {F : Type} [Field F] [Finite F] [CharP F 2]
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {G : Type} [Group G]
    (σ : SL(r + 2, F) →* G) (κ : spinGroup (quadMinus (r + 2) F b c) →* G)
    (hκ : Function.Injective κ)
    (hagree : ∀ k : Fin r, (σ.comp (blockSL2 F (r + 1) k.succ)).range =
      (CurtisTits.rankOne (minusDatum (r + 2) hirr).rootGroup k.castSucc).map κ)
    (U : Fin (r + 2) → Subgroup G)
    (hU : ∀ k : Fin (r + 1), U (Fin.castSucc k) = (σ.comp (blockSL2 F (r + 1) k)).range)
    (hUlast : U (Fin.last (r + 1)) =
      (CurtisTits.rankOne (minusDatum (r + 2) hirr).rootGroup (Fin.last r)).map κ) :
    ∀ i j : Fin (r + 2), i.val + 3 = r + 3 → j.val + 2 = r + 3 →
      ∃ W, TwistedB2BlockStandardPair hirr W (U i) (U j) := by
  have := fact_shortField hirr
  intro i j hi hj
  have hiL : i = Fin.castSucc (Fin.last r) := Fin.ext (by
    simp only [Fin.val_castSucc, Fin.val_last]
    omega)
  have hjL : j = Fin.last (r + 1) := Fin.ext (by
    simp only [Fin.val_last]
    omega)
  let k : Fin r := ⟨r - 1, by omega⟩
  have hkval : (k : ℕ) = r - 1 := rfl
  have hks : k.succ = Fin.last r := Fin.ext (by
    simp only [Fin.val_succ, Fin.val_last, hkval]
    omega)
  have hUL : U i =
      (CurtisTits.rankOne (minusDatum (r + 2) hirr).rootGroup k.castSucc).map κ := by
    rw [hiL, ← hks, hU k.succ, hagree k]
  have hUS : U j =
      (CurtisTits.rankOne (minusDatum (r + 2) hirr).rootGroup (Fin.last r)).map κ := by
    rw [hjL, hUlast]
  rw [hUL, hUS]
  obtain ⟨W, hW⟩ := twistedB2BlockStandardPair_minusDatum_even (F := F) (b := b) (c := c) hirr
    (n := r + 2) (by omega) (i := k.castSucc) (j := Fin.last r)
    (by simp only [Fin.val_castSucc, hkval]; omega)
    (by simp only [Fin.val_last])
  exact ⟨W.map κ, TwistedB2Model.StandardPair.map hW κ hκ⟩

theorem weakCT_spinMinus_even_of_charts {r f : ℕ} (hr : 2 ≤ r) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hF : Nat.card F = 2 ^ f) (hq : 4 ≤ Nat.card F) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {G : Type} [Group G]
    (σ : SL(r + 2, F) →* G) (hσ : σ.ker ≤ Subgroup.center SL(r + 2, F))
    (κ : spinGroup (quadMinus (r + 2) F b c) →* G) (hκ : Function.Injective κ)
    (hagree : ∀ k : Fin r, (σ.comp (blockSL2 F (r + 1) k.succ)).range =
      (CurtisTits.rankOne (minusDatum (r + 2) hirr).rootGroup k.castSucc).map κ)
    (hcross : ∀ a ∈ (σ.comp (blockSL2 F (r + 1) 0)).range,
      ∀ g ∈ (CurtisTits.rankOne (minusDatum (r + 2) hirr).rootGroup (Fin.last r)).map κ,
        a * g = g * a) :
    ∃ Ψ : spinGroup (quadMinus (r + 3) F b c) →* G,
      Ψ.ker ≤ Subgroup.center (spinGroup (quadMinus (r + 3) F b c)) ∧
      Ψ.range = σ.range ⊔ κ.range := by
  have hf : 1 ≤ f := by
    by_contra h
    have h0 : f = 0 := by omega
    have h1 : 2 ^ f = 1 := by rw [h0]; simp
    omega
  have hadm : CFSG.Open.StatedLieAdmissible .POmegaMinus (r + 3) 2 f :=
    ⟨Nat.prime_two, hf, by omega⟩
  let U : Fin (r + 2) → Subgroup G :=
    Fin.lastCases (motive := fun _ => Subgroup G)
      ((CurtisTits.rankOne (minusDatum (r + 2) hirr).rootGroup (Fin.last r)).map κ)
      (fun k : Fin (r + 1) => (σ.comp (blockSL2 F (r + 1) k)).range)
  have hU : ∀ k : Fin (r + 1), U (Fin.castSucc k) = (σ.comp (blockSL2 F (r + 1) k)).range :=
    fun k => Fin.lastCases_castSucc k
  have hUlast : U (Fin.last (r + 1)) =
      (CurtisTits.rankOne (minusDatum (r + 2) hirr).rootGroup (Fin.last r)).map κ :=
    Fin.lastCases_last
  have hgens : (⨆ k, U k) = σ.range ⊔ κ.range :=
    le_antisymm (omc_iSup_le hirr σ κ U hU hUlast)
      (omc_le_iSup hr hirr σ κ hagree U hU hUlast)
  obtain ⟨Ψ, hker, hrange⟩ := omc_recog (n := r + 3) hadm hF hq hirr U
    (omc_comm hirr σ κ hagree hcross U hU hUlast)
    (fun i j hij hj =>
      exists_linearBlockStandardPair_of_blockSL2_frame σ hσ U hU i j hij (by omega))
    (omc_tw hr hirr σ κ hκ hagree U hU hUlast)
  exact ⟨Ψ, hker, hrange.trans hgens⟩

end CFSG.ClassicalInvolution.WeakCT

end
