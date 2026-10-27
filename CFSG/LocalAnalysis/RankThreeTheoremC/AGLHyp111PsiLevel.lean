module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3DataU
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3ReducedA
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M H : Subgroup G}

theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwoDataU.exists_caseTwo_not_le
    (hOut : KFactOutCyclic) (hS : KFactSeitzCyc)
    {P : Sylow p G} {R : Subgroup G} {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    (hd : D1CaseTwoDataU p P M H R Rbar) :
    ∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧
      ¬ L ≤ d1X0 p M H ∧ IsCaseTwoGroup p L := by
  obtain ⟨L, hL, hLX⟩ := hd.cfg.red.exists_not_le_of_caseTwo_of_exists_component
    (kFactCycAut_of_kFactOutCyclic hOut _ _ _ _ hd.cfg.red hd.cfg.catalog) hd.cyclic
    hd.cfg.exists_isComponentOf
  exact ⟨L, hL, hLX,
    hd.cfg.red.isCaseTwoGroup_of_not_le3 hd.cfg.catalog hOut hS hd.cyclic hd.rank hL hLX⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
