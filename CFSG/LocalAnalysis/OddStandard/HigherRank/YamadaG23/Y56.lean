module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56One
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56Iso
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56Two

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y56_fact (c : Ctx5 G L) (hH : F33Hyp c.s c.e) : c.Fact56 :=
  ⟨⟨y56_normalizer_Q c hH, y56_H_inf_C4 c hH, y56_conjClass_C4 c hH, y56_secProp c hH⟩,
    y56_C0_le_C4 c hH, y56_comm_C1_C4 c hH⟩

end CFSG.OddStandard.HigherRank.YamadaG23
