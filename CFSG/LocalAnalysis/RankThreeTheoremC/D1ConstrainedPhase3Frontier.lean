module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedPhase3Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedClose3Klingen

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.AGLEmbedding (D1Extremal Asc81bEightFour D1NoXBlock HasKlingenData)

variable {G : Type} [Group G] [Finite G]

structure D1ConstrainedPhase3Residues3 (G : Type) [Group G] [Finite G] : Prop where
  klingen : D1CaseThreeKlingen3 G
  weakBlock : D1ConstrainedWeakBlockResidue3 G

theorem theoremD1_of_phase3_residues (hS : Setting G) (hK3 : KFactsA3 G)
    (hnone : D1ComponentAlphaNone3 G) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (h1s : D1CaseOneSmall3 G) (h2 : D1CaseTwo3 G) (h3 : D1CaseThreeNotKlingen3 G)
    (h : D1ConstrainedPhase3Residues3 G) : TheoremD1 G := by
  have hcomp : D1ComponentCaseInd3 G :=
    d1ComponentCaseInd3_of_cases hK3 h1s h2 (d1CaseThree3_of_klingen h3 h.klingen)
  exact theoremD1_of_extremalCase3 hS (d1ExtremalCase3_of_cases_ind'
    (d1ConstrainedCaseInd3_of_phase3 hK3 hnone hcomp h84 hD2 h.weakBlock) hcomp)

theorem d1ConstrainedPhase3Residues3_of_theoremD1 (hD1 : TheoremD1 G) :
    D1ConstrainedPhase3Residues3 G :=
  ⟨d1CaseThreeKlingen3_of_theoremD1 hD1, d1ConstrainedWeakBlockResidue3_of_theoremD1 hD1⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
