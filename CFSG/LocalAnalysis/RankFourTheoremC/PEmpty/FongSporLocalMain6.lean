module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalMain5
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigRows7
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigRows8
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottSporUniqueRankCo2

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

structure OpenRows6 : Prop where
  j4_31 : KFactSporLocalRow .J4 31
  j4_43 : KFactSporLocalRow .J4 43

theorem openRows5_of_openRows6
    (h : OpenRows6) : OpenRows5 where
  j4_7 := row_J4_7
  j4_31 := h.j4_31
  j4_43 := h.j4_43
  co2_11 := row_Co2_11
  hn_11 := row_HN_11

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
