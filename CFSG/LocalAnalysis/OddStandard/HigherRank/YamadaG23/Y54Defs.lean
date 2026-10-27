module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YCtx

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

abbrev f4P (s : Setting3 G L) : Subgroup G := s.fr.F ⊔ zpowers s.t

abbrev f4X (s : Setting3 G L) : Subgroup G :=
  normalizer ((s.fr.F ⊔ zpowers s.t : Subgroup G) : Set G)

abbrev f4Y (s : Setting3 G L) : Subgroup G := centIn (f4X s) s.fr.F

abbrev f4X0 (s : Setting3 G L) : Subgroup G := centIn s.H s.fr.F

abbrev f4N (s : Setting3 G L) : Subgroup G := normIn s.H s.fr.F

theorem f4_C3_eq (s : Setting3 G L) : C3 s = pCoreOf 2 ⁅f4Y s, f4N s⁆ ⊔ f4P s := rfl

end CFSG.OddStandard.HigherRank.YamadaG23
