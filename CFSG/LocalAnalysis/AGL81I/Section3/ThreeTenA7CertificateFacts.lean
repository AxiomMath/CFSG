module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123SylowA7
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenRankTwoSL

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12

theorem a7_normalizer_card_seven (Q : Subgroup CFSG.QuasithinUnique.L246.C123.A7)
    (hQ : Nat.card Q = 7) :
    Nat.card (Subgroup.normalizer (Q : Set CFSG.QuasithinUnique.L246.C123.A7)) = 21 := by
  exact CFSG.QuasithinUnique.L246.C123.normalizer_card_of_card_seven Q hQ

end CFSG.LocalAnalysis.AGL81I.Section3
