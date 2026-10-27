module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Vocab

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

variable {X : Type} [Group X] [Finite X]

abbrev barO2 (L : Subgroup X) : Subgroup (X ⧸ CFSG.pCore 2 X) :=
  L.map (QuotientGroup.mk' (CFSG.pCore 2 X))

theorem IsC2.component {L : Subgroup X} (hL : IsC2 L) :
    CFSG.Open.IsComponentOf (barO2 L) ⊤ := hL.2.2

end CFSG.LocalAnalysis.RankThreeUC.S15
