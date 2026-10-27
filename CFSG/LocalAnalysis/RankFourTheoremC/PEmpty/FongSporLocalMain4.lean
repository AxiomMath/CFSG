module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalMain3
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ShultSporLocalZCRows
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ShultSporLocalZCRowsJ2
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottSporOddCentHe

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

structure OpenRows4 : Prop where
  j4_5 : KFactSporLocalRow .J4 5
  j4_7 : KFactSporLocalRow .J4 7
  j4_23 : KFactSporLocalRow .J4 23
  j4_31 : KFactSporLocalRow .J4 31
  j4_43 : KFactSporLocalRow .J4 43
  hs_7 : KFactSporLocalRow .HS 7
  ru_7 : KFactSporLocalRow .Ru 7
  ru_13 : KFactSporLocalRow .Ru 13
  suz_11 : KFactSporLocalRow .Suz 11
  suz_13 : KFactSporLocalRow .Suz 13
  on_5 : KFactSporLocalRow .ONan 5
  on_31 : KFactSporLocalRow .ONan 31
  co2_11 : KFactSporLocalRow .Co2 11
  co2_23 : KFactSporLocalRow .Co2 23
  hn_7 : KFactSporLocalRow .HN 7
  hn_11 : KFactSporLocalRow .HN 11
  ly_7 : KFactSporLocalRow .Ly 7
  ly_31 : KFactSporLocalRow .Ly 31
  th_13 : KFactSporLocalRow .Th 13
  th_31 : KFactSporLocalRow .Th 31

theorem openRows3_of_openRows4
    (h : OpenRows4) : OpenRows3 where
  m22_5 := row_M22_5
  m22_7 := row_M22_7
  m23_5 := row_M23_5
  j2_7 := row_J2_7
  j4_5 := h.j4_5
  j4_7 := h.j4_7
  j4_23 := h.j4_23
  j4_31 := h.j4_31
  j4_43 := h.j4_43
  hs_7 := h.hs_7
  he_17 := row_He_17
  ru_7 := h.ru_7
  ru_13 := h.ru_13
  suz_11 := h.suz_11
  suz_13 := h.suz_13
  on_5 := h.on_5
  on_31 := h.on_31
  co2_11 := h.co2_11
  co2_23 := h.co2_23
  hn_7 := h.hn_7
  hn_11 := h.hn_11
  ly_7 := h.ly_7
  ly_31 := h.ly_31
  th_13 := h.th_13
  th_31 := h.th_31

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
