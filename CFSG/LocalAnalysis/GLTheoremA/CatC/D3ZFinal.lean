module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3PRes
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3IInnerHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ITitsD4
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3IField
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZField
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZCase
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZL10
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZA4

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section Ys04Z

theorem ys04_of_levi_regular'
    (hL : D3InnerLevi) (hR : D3A4Regular) (hN : D3CaseTwoOne) : YS04 :=
  ys04_of_regular (d3InnerInvolution_of_sylow (d3InnerSylow_of_levi hL)) d3FieldInvolution_holds hR hN

theorem ys04_of_levi_regular_four
    (hL : D3InnerLevi) (hR : D3A4Regular) (hN : D3CaseTwoOneFour) : YS04 :=
  ys04_of_levi_regular' hL hR (d3CaseTwoOne_of_four hN)

theorem ys04_of_a4regular_four
    (hR : D3A4Regular) (hN : D3CaseTwoOneFour) : YS04 :=
  ys04_of_levi_regular_four d3InnerLevi_holds hR hN

end Ys04Z

end CFSG.LocalAnalysis.GLTheoremA
