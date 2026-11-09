module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreWDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Dickson.Sec6.Up34Exc

theorem exc3core_wCheck_E8_0_p0 :
    exc3core_wCheck .E8 241 exc3core_dngE8 exc3core_dngE8
      (((RD.allVecs Tag.E8.rank).drop 0).take 205) = true := by
  decide +kernel

theorem exc3core_wCheck_E8_0_p1 :
    exc3core_wCheck .E8 241 exc3core_dngE8 exc3core_dngE8
      (((RD.allVecs Tag.E8.rank).drop 205).take 205) = true := by
  decide +kernel

theorem exc3core_wCheck_E8_0_p2 :
    exc3core_wCheck .E8 241 exc3core_dngE8 exc3core_dngE8
      (((RD.allVecs Tag.E8.rank).drop 410).take 205) = true := by
  decide +kernel

theorem exc3core_wCheck_E8_0_p3 :
    exc3core_wCheck .E8 241 exc3core_dngE8 exc3core_dngE8
      (((RD.allVecs Tag.E8.rank).drop 615).take 205) = true := by
  decide +kernel

theorem exc3core_wCheck_E8_0_p4 :
    exc3core_wCheck .E8 241 exc3core_dngE8 exc3core_dngE8
      (((RD.allVecs Tag.E8.rank).drop 820).take 205) = true := by
  decide +kernel

theorem exc3core_wCheck_E8_0_p5 :
    exc3core_wCheck .E8 241 exc3core_dngE8 exc3core_dngE8
      (((RD.allVecs Tag.E8.rank).drop 1025).take 205) = true := by
  decide +kernel

theorem exc3core_wCheck_E8_0_p6 :
    exc3core_wCheck .E8 241 exc3core_dngE8 exc3core_dngE8
      (((RD.allVecs Tag.E8.rank).drop 1230).take 205) = true := by
  decide +kernel

theorem exc3core_wCheck_E8_0_p7 :
    exc3core_wCheck .E8 241 exc3core_dngE8 exc3core_dngE8
      (((RD.allVecs Tag.E8.rank).drop 1435).take 206) = true := by
  decide +kernel

theorem exc3core_wCheck_E8_0 :
    exc3core_wCheck .E8 241 exc3core_dngE8 exc3core_dngE8
      (((RD.allVecs Tag.E8.rank).drop (1641 * 0)).take 1641) = true :=
  (exc3core_wCheck_join (a := 1641 * 0) (b := 1435) (c := 206) (exc3core_wCheck_join (a := 1641 * 0) (b := 1230) (c := 205) (exc3core_wCheck_join (a := 1641 * 0) (b := 1025) (c := 205) (exc3core_wCheck_join (a := 1641 * 0) (b := 820) (c := 205) (exc3core_wCheck_join (a := 1641 * 0) (b := 615) (c := 205) (exc3core_wCheck_join (a := 1641 * 0) (b := 410) (c := 205) (exc3core_wCheck_join (a := 1641 * 0) (b := 205) (c := 205) exc3core_wCheck_E8_0_p0 exc3core_wCheck_E8_0_p1) exc3core_wCheck_E8_0_p2) exc3core_wCheck_E8_0_p3) exc3core_wCheck_E8_0_p4) exc3core_wCheck_E8_0_p5) exc3core_wCheck_E8_0_p6) exc3core_wCheck_E8_0_p7)

theorem exc3core_wCheck_E8_1_p0 :
    exc3core_wCheck .E8 241 exc3core_dngE8 exc3core_dngE8
      (((RD.allVecs Tag.E8.rank).drop 1641).take 205) = true := by
  decide +kernel

theorem exc3core_wCheck_E8_1_p1 :
    exc3core_wCheck .E8 241 exc3core_dngE8 exc3core_dngE8
      (((RD.allVecs Tag.E8.rank).drop 1846).take 205) = true := by
  decide +kernel

theorem exc3core_wCheck_E8_1_p2 :
    exc3core_wCheck .E8 241 exc3core_dngE8 exc3core_dngE8
      (((RD.allVecs Tag.E8.rank).drop 2051).take 205) = true := by
  decide +kernel

theorem exc3core_wCheck_E8_1_p3 :
    exc3core_wCheck .E8 241 exc3core_dngE8 exc3core_dngE8
      (((RD.allVecs Tag.E8.rank).drop 2256).take 205) = true := by
  decide +kernel

theorem exc3core_wCheck_E8_1_p4 :
    exc3core_wCheck .E8 241 exc3core_dngE8 exc3core_dngE8
      (((RD.allVecs Tag.E8.rank).drop 2461).take 205) = true := by
  decide +kernel

theorem exc3core_wCheck_E8_1_p5 :
    exc3core_wCheck .E8 241 exc3core_dngE8 exc3core_dngE8
      (((RD.allVecs Tag.E8.rank).drop 2666).take 205) = true := by
  decide +kernel

theorem exc3core_wCheck_E8_1_p6 :
    exc3core_wCheck .E8 241 exc3core_dngE8 exc3core_dngE8
      (((RD.allVecs Tag.E8.rank).drop 2871).take 205) = true := by
  decide +kernel

theorem exc3core_wCheck_E8_1_p7 :
    exc3core_wCheck .E8 241 exc3core_dngE8 exc3core_dngE8
      (((RD.allVecs Tag.E8.rank).drop 3076).take 206) = true := by
  decide +kernel

theorem exc3core_wCheck_E8_1 :
    exc3core_wCheck .E8 241 exc3core_dngE8 exc3core_dngE8
      (((RD.allVecs Tag.E8.rank).drop (1641 * 1)).take 1641) = true :=
  (exc3core_wCheck_join (a := 1641 * 1) (b := 1435) (c := 206) (exc3core_wCheck_join (a := 1641 * 1) (b := 1230) (c := 205) (exc3core_wCheck_join (a := 1641 * 1) (b := 1025) (c := 205) (exc3core_wCheck_join (a := 1641 * 1) (b := 820) (c := 205) (exc3core_wCheck_join (a := 1641 * 1) (b := 615) (c := 205) (exc3core_wCheck_join (a := 1641 * 1) (b := 410) (c := 205) (exc3core_wCheck_join (a := 1641 * 1) (b := 205) (c := 205) exc3core_wCheck_E8_1_p0 exc3core_wCheck_E8_1_p1) exc3core_wCheck_E8_1_p2) exc3core_wCheck_E8_1_p3) exc3core_wCheck_E8_1_p4) exc3core_wCheck_E8_1_p5) exc3core_wCheck_E8_1_p6) exc3core_wCheck_E8_1_p7)


end CFSG.LocalAnalysis.GLTheoremA.I167

end
