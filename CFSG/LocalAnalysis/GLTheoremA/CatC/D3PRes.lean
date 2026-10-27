module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3FRes
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3PField
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3PBorMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section D3PRes

theorem ys04_of_fixed
    (hI : D3InnerInvolution) (hF : D3FieldInvolution) (hA4 : D3A4Fixed)
    (hN : D3CaseTwoOne) : YS04 :=
  ys04_of_residual ⟨hI, hF, d3FixedPointFree_of_fixed hI hF hA4 hN⟩

theorem ys04_of_regular
    (hI : D3InnerInvolution) (hF : D3FieldInvolution)
    (hR : D3A4Regular) (hN : D3CaseTwoOne) : YS04 :=
  ys04_of_fixed hI hF (d3A4Fixed_of_regular hR) hN

end D3PRes

end CFSG.LocalAnalysis.GLTheoremA
