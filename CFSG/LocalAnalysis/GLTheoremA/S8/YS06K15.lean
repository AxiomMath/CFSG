module

public import CFSG.LocalAnalysis.GLTheoremA.S8.YS06Cat15
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431KSpor
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431KY
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430Main
public import CFSG.LocalAnalysis.GLTheoremA.S8.YS06Cat13

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section Ys06K15


theorem S8Cat15Inputs.toS8Cat13InputsK
    (h30 : I1430Res) (hY : I1431YRes) (hI3 : I1431Res3) {G : Type} [Group G]
    [Finite G] {p : ℕ} (h : S8Cat15Inputs G p) : S8Cat13Inputs G p where
  i1017 := h.i1017
  i1016Row := h.i1016Row
  i301A := h.i301A
  in84_i1430 := S8.L84.I1430At_of_facts G h30.cls h30.alt h30.suz h30.on h30.chev
  in84_i1431 := h.in84_i1431
  in8910_i301B := h.in8910_i301B
  in8910_i1420 := h.in8910_i1420
  in8910_i1431 := I1431Y.in8910_i1431_of_factsK i1431SporSK_holds hI3.1 hI3.2 hY.d4 hY.u5 hY.u4 G
  in8910_i1432 := h.in8910_i1432

end Ys06K15

end CFSG.LocalAnalysis.GLTheoremA

end
