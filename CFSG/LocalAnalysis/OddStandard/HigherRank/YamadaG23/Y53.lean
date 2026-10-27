module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y53Jr
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y53N
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YSec5S

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y53_fact {c : Ctx5 G L} (hH : F33Hyp c.s c.e) : c.Fact53 :=
  ⟨y5_normN_Aqt hH, y5_normN_C0 hH, y53_jr hH⟩

end CFSG.OddStandard.HigherRank.YamadaG23
