module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Chev
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedPhase3Frontier

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open

structure D1FrontierResidues3 (G : Type) [Group G] [Finite G] : Prop where
  constrained : D1ConstrainedPhase3Residues3 G
  oneSmall : D1CaseOneSmall3 G
  two : D1CaseTwo3 G
  caseThree : D1CaseThreeFineResidues3 G

variable {G : Type} [Group G] [Finite G]

theorem D1FrontierResidues3.theoremD1 (hS : Setting G) (hK3 : KFactsA3 G)
    (hnone : D1ComponentAlphaNone3 G) (hk : D1CaseThreeKFacts3) (hr : D1CaseThreeReeFacts3)
    (hc : D1CaseThreeChevFacts3) (h : D1FrontierResidues3 G) : TheoremD1 G :=
  theoremD1_of_phase3_residues hS hK3 hnone hc.g28a15.eightFour hc.g28a15.noXBlock h.oneSmall
    h.two (h.caseThree.notKlingen hk hr hc) h.constrained

theorem d1FrontierResidues3_of_theoremD1 (hD1 : TheoremD1 G) : D1FrontierResidues3 G := by
  have hm := d1MergedResidues3_of_theoremD1 hD1
  exact ⟨d1ConstrainedPhase3Residues3_of_theoremD1 hD1, hm.oneSmall, hm.two,
    d1CaseThreeFineResidues3_of_theoremD1 hD1⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
