module

public import CFSG.LocalAnalysis.GLTheoremA.S8.YS06Cat10
public import CFSG.LocalAnalysis.GLTheoremA.CatB.CfgIRowsMcL
public import CFSG.LocalAnalysis.GLTheoremA.CatB.CfgIRowsHN
public import CFSG.LocalAnalysis.GLTheoremA.CatB.CfgIRowsD4
public import CFSG.LocalAnalysis.GLTheoremA.CatB.CfgIRowsU43
public import CFSG.LocalAnalysis.GLTheoremA.CatB.CfgIRowsSuz
public import CFSG.LocalAnalysis.GLTheoremA.CatB.CfgIRowsFi24

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.CfgI

open CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremA

section Certs


theorem cfgIRes_of_m3 (hm3 : CfgIRankRow 3 S8.Row.m3) : CfgIRes := by
  intro p row hth hco2 hp
  cases row with
  | ly => subst hp; exact cfgIRank_ly_three
  | co2 => exact absurd rfl hco2
  | co1 => subst hp; exact cfgIRank_co1_three
  | fi24 => subst hp; exact cfgIRank_fi24_three
  | fi24h => subst hp; exact cfgIRank_fi24h_three
  | suz => subst hp; exact cfgIRank_suz_three
  | suzh => subst hp; exact cfgIRank_suzh_three
  | th => exact absurd rfl hth
  | m3 => subst hp; exact hm3
  | m5 => subst hp; exact cfgIRank_m5_five


theorem cfgIRes_holds : CfgIRes :=
  cfgIRes_of_m3 cfgIRank_m3_three

end Certs

end CFSG.LocalAnalysis.GLTheoremA.S8.CfgI
