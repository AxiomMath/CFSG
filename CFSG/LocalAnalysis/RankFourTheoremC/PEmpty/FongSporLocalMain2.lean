module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalPermRows

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

structure OpenRows2 : Prop where
  m22_5 : KFactSporLocalRow .M22 5
  m22_7 : KFactSporLocalRow .M22 7
  m23_5 : KFactSporLocalRow .M23 5
  j2_7 : KFactSporLocalRow .J2 7
  j3_5 : KFactSporLocalRow .J3 5
  j4_5 : KFactSporLocalRow .J4 5
  j4_7 : KFactSporLocalRow .J4 7
  j4_23 : KFactSporLocalRow .J4 23
  j4_31 : KFactSporLocalRow .J4 31
  j4_43 : KFactSporLocalRow .J4 43
  hs_7 : KFactSporLocalRow .HS 7
  mcl_7 : KFactSporLocalRow .McL 7
  he_17 : KFactSporLocalRow .He 17
  ru_7 : KFactSporLocalRow .Ru 7
  ru_13 : KFactSporLocalRow .Ru 13
  suz_7 : KFactSporLocalRow .Suz 7
  suz_11 : KFactSporLocalRow .Suz 11
  suz_13 : KFactSporLocalRow .Suz 13
  on_5 : KFactSporLocalRow .ONan 5
  on_31 : KFactSporLocalRow .ONan 31
  co2_7 : KFactSporLocalRow .Co2 7
  co2_11 : KFactSporLocalRow .Co2 11
  co2_23 : KFactSporLocalRow .Co2 23
  co3_7 : KFactSporLocalRow .Co3 7
  co3_11 : KFactSporLocalRow .Co3 11
  hn_7 : KFactSporLocalRow .HN 7
  hn_11 : KFactSporLocalRow .HN 11
  ly_7 : KFactSporLocalRow .Ly 7
  ly_31 : KFactSporLocalRow .Ly 31
  th_13 : KFactSporLocalRow .Th 13
  th_31 : KFactSporLocalRow .Th 31

theorem openRows_of_openRows2
    (h : OpenRows2) : OpenRows where
  m12_5 := row_M12_5
  m22_5 := h.m22_5
  m22_7 := h.m22_7
  m23_5 := h.m23_5
  m23_7 := row_M23_7
  m24_5 := row_M24_5
  m24_7 := row_M24_7
  j2_7 := h.j2_7
  j3_5 := h.j3_5
  j4_5 := h.j4_5
  j4_7 := h.j4_7
  j4_23 := h.j4_23
  j4_31 := h.j4_31
  j4_43 := h.j4_43
  hs_7 := h.hs_7
  mcl_7 := h.mcl_7
  he_17 := h.he_17
  ru_7 := h.ru_7
  ru_13 := h.ru_13
  suz_7 := h.suz_7
  suz_11 := h.suz_11
  suz_13 := h.suz_13
  on_5 := h.on_5
  on_31 := h.on_31
  co2_7 := h.co2_7
  co2_11 := h.co2_11
  co2_23 := h.co2_23
  co3_7 := h.co3_7
  co3_11 := h.co3_11
  hn_7 := h.hn_7
  hn_11 := h.hn_11
  ly_7 := h.ly_7
  ly_31 := h.ly_31
  th_13 := h.th_13
  th_31 := h.th_31

theorem kFactSporLocal_of_rows2
    (h : OpenRows2) : KFactSporLocal :=
  kFactSporLocal_of_rows (openRows_of_openRows2 h)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
