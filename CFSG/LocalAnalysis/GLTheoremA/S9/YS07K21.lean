module

public import CFSG.LocalAnalysis.GLTheoremA.S9.YS07Cat21
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431KSpor
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431KMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1429Red
public import CFSG.LocalAnalysis.GLTheoremA.S9.YS07Cat19

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section Ys07K21


theorem S9Cat21Inputs.toS9Cat19InputsK
    (hI : I1431Res3) {G : Type} [Group G] [Finite G] {p : ℕ}
    (h : S9Cat21Inputs G p) : S9Cat19Inputs G p where
  i137 := h.i137
  i137_3 := h.i137_3
  i141 := h.i141
  i2610 := h.i2610
  i1431 := i1431ClAt_of_XK i1431SporSK_holds hI.1 G (i1429At_of_residual hI.2 G)

end Ys07K21

end CFSG.LocalAnalysis.GLTheoremA

end
