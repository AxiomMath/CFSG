module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7Defs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

abbrev y7bCS3 (c : Ctx7 G L) : Subgroup G := centralizerSection (M3 c.s) (V1 c.e)

abbrev y7bCS5 (c : Ctx7 G L) : Subgroup G := centralizerSection (M5 c.e) (V1 c.e)

end CFSG.OddStandard.HigherRank.YamadaG23
