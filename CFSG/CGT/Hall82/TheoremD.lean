module

public import CFSG.CGT.Hall82.DCaseB

public section

namespace CFSG.CGT.Hall82.Setting

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec19
open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Hexa

variable {G : Type} [Group G] [Finite G] {M L : Subgroup G} {R : Subgroup G}
  {rep : Fin 64 → G}

theorem inCatalog_of_centralizer_eq_bot
    (hNode : CFSG.CGT.Timmesfeld75.NodeStatement) (S : Setting G M L) (hF : ModelFacts)
    (hD : DModelFacts) (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥) :
    CFSG.Assembly.InCatalog G := by
  by_cases hcM : Subgroup.centralizer ({rep 5} : Set G) ≤ M
  · exact S.inCatalog_of_centralizer_le hNode hF hD hc hC1 hcM
  · exact S.inCatalog_of_not_centralizer_le hF hD hc hC1 hcM

end CFSG.CGT.Hall82.Setting
