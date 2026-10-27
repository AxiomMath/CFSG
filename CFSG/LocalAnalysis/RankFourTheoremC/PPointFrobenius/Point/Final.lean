module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Point.Norm

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem ptConclusion_of_kfacts (hk : PtKFacts) (hs : PtSchurBound) (hG : FrobGlobal G)
    (hl : PtLocal p P M x) : PtConclusion p P M x := by
  haveI : Fact p.Prime := ⟨hl.loc.beta.1⟩
  exact ⟨pt_structure hk hs hG hl.toPtPoint, pt_norm hk hs hG hl⟩

theorem ysPPointCentralizers_of_kfacts (hk : PtKFacts) (hs : PtSchurBound) :
    CFSG.Yardstones.Md8ed6d263d89.YSPPointCentralizers :=
  ysPPointCentralizers_of_local fun _ _ _ hG _ _ _ _ hl => ptConclusion_of_kfacts hk hs hG hl

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
