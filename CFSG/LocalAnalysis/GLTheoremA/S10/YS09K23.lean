module

public import CFSG.LocalAnalysis.GLTheoremA.S10.YS09Cat23
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431KMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431KSpor
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1429Red
public import CFSG.LocalAnalysis.GLTheoremA.S10.YS09Cat22

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section Ys09K23


theorem S10Cat23Inputs.toS10Cat22InputsK
    (hI : I1431Res3) {G : Type} [Group G] [Finite G] {p : ℕ}
    (h : S10Cat23Inputs G p) : S10Cat22Inputs G p where
  i155x := h.i155x
  u48res := h.u48res
  multaRes := h.multaRes
  i2023 := h.i2023
  i156 := h.i156
  i2021 := h.i2021
  i263 := h.i263
  i265 := h.i265
  i2018 := h.i2018
  i148d := h.i148d
  i1431 := i1431ClAt_of_XK i1431SporSK_holds hI.1 G (i1429At_of_residual hI.2 G)
  i2015 := h.i2015
  i114 := h.i114
  i158 := h.i158
  i141 := h.i141
  substable := h.substable
  i171 := h.i171
  u6d0 := h.u6d0
  i14chev := h.i14chev
  i144one := h.i144one
  i1428 := h.i1428
  i266 := h.i266
  i263a := h.i263a
  i148f := h.i148f
  u62t9 := h.u62t9

end Ys09K23

end CFSG.LocalAnalysis.GLTheoremA

end
