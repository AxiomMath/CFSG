module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalMain4
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigJ4
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigRows
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigRows2
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigRows4
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigRows5
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigRows6
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottSporOddCentCo2
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottSporOddCentRu
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottSporOddCentSuz
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ShultSporLocalGenURu
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ShultSporLocalZCRowsHS

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

structure OpenRows5 : Prop where
  j4_7 : KFactSporLocalRow .J4 7
  j4_31 : KFactSporLocalRow .J4 31
  j4_43 : KFactSporLocalRow .J4 43
  co2_11 : KFactSporLocalRow .Co2 11
  hn_11 : KFactSporLocalRow .HN 11

theorem openRows4_of_openRows5
    (h : OpenRows5) : OpenRows4 where
  j4_5 := row_J4_5
  j4_7 := h.j4_7
  j4_23 := row_J4_23
  j4_31 := h.j4_31
  j4_43 := h.j4_43
  hs_7 := row_HS_7
  ru_7 := row_Ru_7
  ru_13 := row_Ru_13
  suz_11 := row_Suz_11
  suz_13 := row_Suz_13
  on_5 := row_ON_5
  on_31 := row_ON_31
  co2_11 := h.co2_11
  co2_23 := row_Co2_23
  hn_7 := row_HN_7
  hn_11 := h.hn_11
  ly_7 := row_Ly_7
  ly_31 := row_Ly_31
  th_13 := row_Th_13
  th_31 := row_Th_31

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
