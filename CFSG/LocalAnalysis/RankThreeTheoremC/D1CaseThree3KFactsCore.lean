module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Residues
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitarySchur
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Unitary
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryAutElemRank
import CFSG.LocalAnalysis.AGLEmbedding.AltCaseThreeK

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.AGLEmbedding (KFactKlingenSpFour KFactP1ThreeLie)

structure D1CaseThreeKFactsCore3Core : Prop where
  p1Lie : KFactP1ThreeLie

structure D1CaseThreeKFactsCore3 : Prop where
  p1Lie : KFactP1ThreeLie
  klingenSpFour : KFactKlingenSpFour
  spor : SporCaseThreeKFactsRank3E3
  sections : SporSectionFacts3
  outSpor : ∀ s : TauCeti.SporadicName, ∀ p : ℕ, p.Prime → p ≠ 2 →
    ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group)


theorem D1CaseThreeKFactsCore3.toKFacts (h : D1CaseThreeKFactsCore3) : D1CaseThreeKFacts3 :=
  ⟨h.p1Lie, h.klingenSpFour, CFSG.AGLEmbedding.altCaseThreeKFacts, h.outSpor, h.spor, h.sections,
    CFSG.AGLEmbedding.kFactUnitarySchur, CFSG.AGLEmbedding.kFactUnitarySylowStructure,
    CFSG.AGLEmbedding.kFactUnitaryAutElemRank⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
