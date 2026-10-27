module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YCtx

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

abbrev y7bW (s : Setting3 G L) : Subgroup G := s.fr.B ⊔ C3 s

abbrev y7bBM (s : Setting3 G L) : Subgroup G := s.fr.B ⊔ M3 s

abbrev y7bX (s : Setting3 G L) : Subgroup G :=
  normalizer (y7bW s : Set G) ⊓ normalizer (M3 s : Set G)

abbrev y7bC (s : Setting3 G L) : Subgroup G := normIn s.H s.fr.B ⊔ M3 s

abbrev y7bX0 (s : Setting3 G L) : Subgroup G := centralizerSection (y7bW s) (M3 s)

abbrev y7bK (s : Setting3 G L) : Subgroup G := y7bX s ⊓ centralizer (cen s.fr.B : Set G)

end CFSG.OddStandard.HigherRank.YamadaG23
