module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YCtx

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

@[expose] def y4S2 (s : Setting3 G L) : Subgroup G := M2 s ⊔ s.fr.S

@[expose] def y4Y0 (s : Setting3 G L) (g : G) : Subgroup G :=
  s.fr.F ⊔ zpowers g ⊔ zpowers s.t

end CFSG.OddStandard.HigherRank.YamadaG23
