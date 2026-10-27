module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54Two
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54R

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y54_fact (c : Ctx5 G L) (hH : F33Hyp c.s c.e) : c.Fact54 :=
  ⟨⟨y54_normalizer_P c hH, y54_H_inf_M3 c hH, y54_conjClass_M3 c hH, y54_secProp c hH⟩,
    ⟨y54_C3_eq_M3 c hH, y54_C0_le_C3 c hH, y54_comm_C1_C3 c hH⟩,
    ⟨y54_K_le_M3 c hH, y54_M2_eq_KB c hH, y54_K_relIndex c hH, y54_R2_le_R3 c hH,
      y54_R2_relIndex c hH⟩⟩

end CFSG.OddStandard.HigherRank.YamadaG23
