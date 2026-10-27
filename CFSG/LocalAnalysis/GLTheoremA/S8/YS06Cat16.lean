module

public import CFSG.LocalAnalysis.GLTheoremA.S8.YS06Cat15
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Row

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure S8Cat16Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i1017 : I1017At G p
  i301A : I301AAt G p
  in84_i1431 : S8.L84.I1431At G
  in8910_i301B : S8.L89.I301BAt G p
  in8910_i1420 : S8.L89.I1420CfgAt G p
  in8910_i1432 : S8.L89.I1432At G

section Ys06Cat16

theorem S8Cat16Inputs.toS8Cat15Inputs
    (hRow : H1017.I1016RowFacts) {G : Type} [Group G] [Finite G] {p : ℕ}
    (h : S8Cat16Inputs G p) : S8Cat15Inputs G p where
  i1017 := h.i1017
  i1016Row := H1017.i1016Row_of_facts (G := G) hRow
  i301A := h.i301A
  in84_i1431 := h.in84_i1431
  in8910_i301B := h.in8910_i301B
  in8910_i1420 := h.in8910_i1420
  in8910_i1432 := h.in8910_i1432

end Ys06Cat16

end CFSG.LocalAnalysis.GLTheoremA
