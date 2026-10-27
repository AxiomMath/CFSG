module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeTransvThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeTransvSmall
public import Certificates.Certificate2012
public import Certificates.Certificate26121
public import Certificates.Certificate26122
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeTransvOmega
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeTransvU42
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenTwelveRanksNotLe
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenTwelveRanksLeOrth
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.Wreathed.OddKernelSylowQuotient
public import CFSG.ClassicalGroups
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsG3
public import CFSG.Goldschmidt.StatementsH
public import CFSG.GroupTheory.PCore.Transport
public import CFSG.GroupTheory.QuasiDihedralFusion.InvolutionCentralizer
public import CFSG.GroupTheory.RegularModuleThree
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.AltCentre
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.TwoGroupExtension
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.AGLEmbedding.LemmaBGlue
public import CFSG.LocalAnalysis.AGLEmbedding.LemmaBGroup
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideBlocksThree
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieUniqueJCompetitor
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaBlock
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeMSide
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLIbAltFive
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Cover
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofComponentLift
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddCentralFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOrthLow
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthSplit
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorInner
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocle
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecOrthFact
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecPGU
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecPair
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecSympMain
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLAllInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspaceComponent
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraComponents
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CZeroLeaves
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenSevenCfgOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3ACentralBaseXQ
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3LinTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3CentralU
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3InnerNotQRankTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenSp4Main
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.G2A5Setting
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.Background.InternalSecIso
public import CFSG.Quasithin.H13.Sp62D3
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch11SecA11Exists
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11SecAFacts04
public import CFSG.Quasithin.Vol2.Ch11SecAVi2
public import CFSG.Quasithin.Vol2.Ch11SecSFacts
public import CFSG.Quasithin.Vol2.Ch11SecSSetup
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenTwelveOneOf
import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.TransvW

open CFSG.Open CFSG.AGLEmbedding Subgroup

@[expose] def KFactTransvU42 : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (Y P : Subgroup A), P ≤ Y →
    ∀ d : TauCeti.ValidLieTypeIndex, (∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .twistedA 3 q) →
    Nonempty (↥Y ≃* (TauCeti.CFSGIndex.lie d).Group) → Nonempty (↥P ≃* Equiv.Perm (Fin 6)) →
    ∀ b : A, Odd (orderOf b) → b ∈ normalizer (Y : Set A) → b ∈ normalizer (P : Set A) →
      (∀ w (hw : w ∈ P), QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨w, hw⟩ ∈
          wSup (↥P ⧸ CFSG.pCore 2 ↥P) → b * w * b⁻¹ * w⁻¹ ∈ pCoreOf 2 P) →
      ∀ y ∈ Y, b * y = y * b

@[expose] def KFactTransvO8m : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (Y P : Subgroup A), P ≤ Y →
    ∀ d d' : TauCeti.ValidLieTypeIndex,
    (∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .twistedD 4 q) →
    (∃ q : TauCeti.PrimePower, q.card = 2 ∧ d'.1 = .B 3 q) →
    Nonempty (↥Y ≃* (TauCeti.CFSGIndex.lie d).Group) →
    Nonempty (↥P ⧸ CFSG.pCore 2 ↥P ≃* (TauCeti.CFSGIndex.lie d').Group) →
    ∀ b : A, Odd (orderOf b) → b ∈ normalizer (Y : Set A) → b ∈ normalizer (P : Set A) →
      (∀ w (hw : w ∈ P), QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨w, hw⟩ ∈
          wSup (↥P ⧸ CFSG.pCore 2 ↥P) → b * w * b⁻¹ * w⁻¹ ∈ pCoreOf 2 P) →
      ∀ y ∈ Y, b * y = y * b

theorem p_eq_two_and_exponent_eq_one {q : TauCeti.PrimePower} (hq : q.card = 2) :
    q.p = 2 ∧ q.exponent = 1 := by
  have hpe : q.p ^ q.exponent = 2 := (TauCeti.PrimePower.card_def q).symm.trans hq
  have hdvd : q.p ∣ 2 := hpe ▸ dvd_pow_self q.p q.exponent_pos.ne'
  have hqp : q.p = 2 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp hdvd
  refine ⟨hqp, ?_⟩
  rw [hqp] at hpe
  exact Nat.pow_right_injective le_rfl (by simpa using hpe)

theorem kFactTransvectionW3_of_cases (hU : KFactTransvU42) (hO : KFactTransvO8m) :
    KFactTransvectionW3 := by
  intro A _ _ Y P hPY hrk hcase b hbo hbY hbP hW
  have hrk' : Open.pRank 3 (⊤ : Subgroup ↥Y) ≤ 3 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact hrk
  rcases hcase with ⟨m, d, d', ⟨q, hq, hD | hTD⟩, hd', hY, hP⟩ | ⟨hYU, hP⟩ | ⟨hY5, hP3⟩
  · exfalso
    obtain ⟨hqp, hqe⟩ := p_eq_two_and_exponent_eq_one hq
    have h4 := TwelveRanksNotLe.four_le_pRank_three_of_isLieOver_D
      (Y := ↥Y) (r := m) ⟨d, ⟨q, hqp, hqe, hD⟩, hY⟩
    omega
  · obtain ⟨hqp, hqe⟩ := p_eq_two_and_exponent_eq_one hq
    have hm4 : 4 ≤ m := by
      have h := d.2
      rw [hTD] at h
      exact (TauCeti.LieTypeIndex.inStandardRange_iff _).1
        ((TauCeti.LieTypeIndex.valid_iff _).1 h).1
    rcases (show m = 4 ∨ 5 ≤ m by omega) with rfl | hm5
    · exact hO A Y P hPY d d' ⟨q, hq, hTD⟩ hd' hY hP b hbo hbY hbP hW
    · exfalso
      have h4 := TwelveRanksLe.four_le_pRank_of_isLieOver_twistedD
        (Y := ↥Y) ⟨d, ⟨q, hqp, hqe, hTD⟩, hY⟩ hm5
      omega
  · rcases hYU with ⟨d, hd, hY⟩ | hY8
    · exact hU A Y P hPY d hd hY hP b hbo hbY hbP hW
    · obtain ⟨eY⟩ := hY8
      obtain ⟨eP⟩ := hP
      exact centralizes_altEight hPY eY eP hbo hbY hbP hW
  · obtain ⟨eY⟩ := hY5
    obtain ⟨eP⟩ := hP3
    exact centralizes_altFive hPY eY eP hbo hbY hbP hW

theorem kFactTransvO8m_holds : KFactTransvO8m := by
  intro A _ _ Y P hPY d d' hd hd' hY hP b hbo hbY hbP hW
  obtain ⟨eY⟩ := hY
  obtain ⟨eP⟩ := hP
  exact centralizes_omegaMinusEight hPY d d' hd hd' eY eP hbo hbY hbP hW

theorem kFactTransvectionW3_of_u42 (hU : KFactTransvU42) : KFactTransvectionW3 :=
  kFactTransvectionW3_of_cases hU kFactTransvO8m_holds

theorem kFactTransvU42_holds :
    KFactTransvU42 := by
  intro A _ _ Y P hPY d hd hY hP b hbo hbY hbP hW
  obtain ⟨eY⟩ := hY
  obtain ⟨eP⟩ := hP
  exact centralizes_u42 hPY d hd eY eP hbo hbY hbP hW

theorem kFactTransvectionW3_holds :
    KFactTransvectionW3 :=
  kFactTransvectionW3_of_u42 kFactTransvU42_holds

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.TransvW
