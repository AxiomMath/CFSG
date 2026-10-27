module

public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup
open scoped MatrixGroups

theorem pRank_le_pRank_of_injective {p : ℕ} (hp : 1 < p) {X Y : Type*} [Group X] [Group Y]
    [Finite X] [Finite Y] (f : X →* Y) (hf : Function.Injective f) :
    CFSG.pRank p X ≤ CFSG.pRank p Y := by
  rw [SectionRank.pRank_eq_open_pRank_top, SectionRank.pRank_eq_open_pRank_top]
  exact (SectionRank.pRank_le_map hp f hf ⊤).trans (SectionRank.pRank_mono hp le_top)

end CFSG.ComponentClassification.FooteLit
