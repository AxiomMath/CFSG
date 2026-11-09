module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreWDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Dickson.Sec6.Up34Exc

theorem exc3core_wCheck_E7_p0 :
    exc3core_wCheck .E7 127 exc3core_uniE7 exc3core_dngE7
      (((RD.allVecs Tag.E7.rank).drop 0).take 273) = true := by
  decide +kernel

theorem exc3core_wCheck_E7_p1 :
    exc3core_wCheck .E7 127 exc3core_uniE7 exc3core_dngE7
      (((RD.allVecs Tag.E7.rank).drop 273).take 273) = true := by
  decide +kernel

theorem exc3core_wCheck_E7_p2 :
    exc3core_wCheck .E7 127 exc3core_uniE7 exc3core_dngE7
      (((RD.allVecs Tag.E7.rank).drop 546).take 273) = true := by
  decide +kernel

theorem exc3core_wCheck_E7_p3 :
    exc3core_wCheck .E7 127 exc3core_uniE7 exc3core_dngE7
      (((RD.allVecs Tag.E7.rank).drop 819).take 273) = true := by
  decide +kernel

theorem exc3core_wCheck_E7_p4 :
    exc3core_wCheck .E7 127 exc3core_uniE7 exc3core_dngE7
      (((RD.allVecs Tag.E7.rank).drop 1092).take 273) = true := by
  decide +kernel

theorem exc3core_wCheck_E7_p5 :
    exc3core_wCheck .E7 127 exc3core_uniE7 exc3core_dngE7
      (((RD.allVecs Tag.E7.rank).drop 1365).take 273) = true := by
  decide +kernel

theorem exc3core_wCheck_E7_p6 :
    exc3core_wCheck .E7 127 exc3core_uniE7 exc3core_dngE7
      (((RD.allVecs Tag.E7.rank).drop 1638).take 273) = true := by
  decide +kernel

theorem exc3core_wCheck_E7_p7 :
    exc3core_wCheck .E7 127 exc3core_uniE7 exc3core_dngE7
      (((RD.allVecs Tag.E7.rank).drop 1911).take 276) = true := by
  decide +kernel

theorem exc3core_wCheck_E7_length : (RD.allVecs Tag.E7.rank).length = 2187 := by
  decide +kernel

theorem exc3core_wCheck_E7 :
    exc3core_wCheck .E7 127 exc3core_uniE7 exc3core_dngE7 (RD.allVecs Tag.E7.rank) = true := by
  have h : exc3core_wCheck .E7 127 exc3core_uniE7 exc3core_dngE7
      (((RD.allVecs Tag.E7.rank).drop 0).take 2187) = true :=
    (exc3core_wCheck_join (a := 0) (b := 1911) (c := 276) (exc3core_wCheck_join (a := 0) (b := 1638) (c := 273) (exc3core_wCheck_join (a := 0) (b := 1365) (c := 273) (exc3core_wCheck_join (a := 0) (b := 1092) (c := 273) (exc3core_wCheck_join (a := 0) (b := 819) (c := 273) (exc3core_wCheck_join (a := 0) (b := 546) (c := 273) (exc3core_wCheck_join (a := 0) (b := 273) (c := 273) exc3core_wCheck_E7_p0 exc3core_wCheck_E7_p1) exc3core_wCheck_E7_p2) exc3core_wCheck_E7_p3) exc3core_wCheck_E7_p4) exc3core_wCheck_E7_p5) exc3core_wCheck_E7_p6) exc3core_wCheck_E7_p7)
  rwa [List.drop_zero, List.take_of_length_le (le_of_eq exc3core_wCheck_E7_length)] at h

theorem exc3core_eCheck_E7 : ∀ d ∈ RD.allVecs Tag.E7.rank,
    exc3core_eCheck .E7 127 exc3core_uniE7 exc3core_dngE7 d = true :=
  List.all_eq_true.1 exc3core_wCheck_E7

end CFSG.LocalAnalysis.GLTheoremA.I167

end
