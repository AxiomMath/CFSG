module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZFinal
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZM3

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section Ys04Z


theorem d3CaseTwoOne_holds
    : D3CaseTwoOne := d3CaseTwoOne_of_four d3CaseTwoOneFour_holds

theorem ys04_of_a4regular
    (hR : D3A4Regular) : YS04 :=
  ys04_of_a4regular_four hR d3CaseTwoOneFour_holds

theorem ys04_of_a4levi
    (hL : D3A4Levi) : YS04 :=
  ys04_of_a4regular (d3A4Regular_of_levi hL)

end Ys04Z

end CFSG.LocalAnalysis.GLTheoremA
