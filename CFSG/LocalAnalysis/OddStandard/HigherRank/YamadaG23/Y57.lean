module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y57C
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y57D
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y57F

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y57_fact (c : Ctx5 G L) (hH : F33Hyp c.s c.e) : c.Fact57 := by
  rcases y57_d_or_td c hH with hd | htd
  · obtain ⟨hV, hle⟩ := y57_V1_A c hH hd
    exact ⟨hle, Or.inl ⟨hV, y57_caseA c hH hd⟩⟩
  · obtain ⟨hV, hle⟩ := y57_V1_B c hH htd
    refine ⟨hle, Or.inr ⟨hV, ⟨⟨fun a b => ?_⟩⟩, y57_caseB_homocyclic c hH htd,
      y57_caseB_inv c hH htd⟩⟩
    exact Subtype.ext (y57_M3_comm c hH _ a.2 _ b.2)

end CFSG.OddStandard.HigherRank.YamadaG23
