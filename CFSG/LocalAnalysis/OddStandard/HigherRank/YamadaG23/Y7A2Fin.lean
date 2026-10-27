module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2SV
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2M4c
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2G
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2Sq

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7a_fact72 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (h71 : c.Fact71) : c.Fact72 :=
  ⟨⟨y7a_M2_eq c hH hF h71, y7a_B_V2_comm c hH hF h71, y7a_B_inf_V2 c hH hF h71,
      (y7a_V2_data c hH hF h71).1, y7a_S_V1_comm c hH hF h71⟩,
    y7a_M4_elemAbelian c hH hF h71, y7a_fact72_3 c hH hF h71, y7a_fact72_4 c hH hF h71⟩

end CFSG.OddStandard.HigherRank.YamadaG23
