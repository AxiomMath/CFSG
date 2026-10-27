module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFStmts
public import CFSG.Quasithin.Background.B15P4Repl
public import CFSG.HardMathSupport.U4FF.BOTransport
public import CFSG.HardMathSupport.U4FF.BOQuad
public import CFSG.HardMathSupport.U4FF.BO4
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.Foundations
public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.Statements
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfig
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscape
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHom
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLarge
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXGen
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ZZPrimeDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFAbs
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B1MoreElevenD
public import CFSG.Quasithin.Background.B1MoreElevenF
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import Certificates.Certificate43
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.Quasithin Subgroup CFSG.HardMathSupport.U4FF

theorem charP_two_of_card_eq_pow {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) : CharP F 2 :=
  ringChar.of_eq (CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq Nat.prime_two hn hF)

theorem partBO_sub {S : Type} [CommGroup S] {n : ℕ} (hn : 1 ≤ n) {F : Type} [Field F] [Finite F]
    {b c : F} (hF : Nat.card F = 2 ^ n) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {L A : Subgroup (MulAut S)} (ε : ↥L ≃* ↥(StatedOmega (StatedQuadMinus 3 F b c)))
    (ψ : S ≃* Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F))
    (hεψ : ∀ (l : ↥L) (s : S), ψ ((l : MulAut S) s) = Multiplicative.ofAdd
      (((ε l : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).mulVec
          (Multiplicative.toAdd (ψ s))))
    (hAN : A ≤ Subgroup.normalizer (L : Set (MulAut S))) {Q : Subgroup (MulAut S)}
    (hQA : Q ≤ A) (hQ : IsElemAbelian2 Q) (hQq : IsQuadratic Q) :
    Nat.card Q * Nat.card (fixV Q) ≤ 2 * Nat.card S := by
  haveI := charP_two_of_card_eq_pow hn hF
  have h := partBO_quadratic hn hF hirr (boSub ψ Q) (bo_add_self ψ hQ) (bo_quad ψ hQq)
    (bo_normalizes ε ψ hεψ hAN hQA)
  rw [boSub_card ψ Q, bo_card_fix ψ Q, bo_card_space ψ] at h
  exact h

theorem partBO_stmt : PartBOStmt := by
  intro S _ _ hS n hn F _ _ b c hF hirr L A ε ψ hεψ hA hAN
  by_contra hcon
  rw [not_le] at hcon
  have hne : A ≠ ⊥ := by
    rintro rfl
    rw [B1.card_bot_mul_card_fixV] at hcon
    omega
  obtain ⟨B, -, hB, hBc⟩ := B1.exists_offender_below (X := A) (A := A)
    ⟨le_rfl, hne, hA⟩ (Nat.card S + 1) (by omega)
  obtain ⟨Q, -, hQ, hQq, hQc, -, -⟩ := exists_quadratic_offender_le hS hB
  have hle := partBO_sub hn hF hirr ε ψ hεψ hAN hQ.1 hQ.2.2.1 hQq
  rw [← hQc] at hBc
  omega

theorem partBO4_stmt : PartBO4Stmt := by
  intro S _ _ hS n hn F _ _ b c hF hirr L A ε ψ hεψ hA hAN hcon
  haveI := charP_two_of_card_eq_pow hn hF
  obtain ⟨hA4, hSC⟩ := hcon
  exact partBO4_sub hn hF hirr (boSub ψ A) (bo_add_self ψ hA) (bo_comm ψ hA)
    (bo_normalizes ε ψ hεψ hAN le_rfl) (by rw [boSub_card ψ A, hA4])
    (by rw [bo_card_space ψ, bo_card_fix ψ A]; exact hSC)

end CFSG.LocalAnalysis.RankThreeUC
