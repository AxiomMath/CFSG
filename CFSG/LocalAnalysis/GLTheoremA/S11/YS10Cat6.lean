module

public import CFSG.LocalAnalysis.GLTheoremA.S11.YS10Cat5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142Main
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142Cyc

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure S11Cat6Inputs (G : Type) [Group G] [Finite G] : Prop where
  i165 : I165At G
  i2315a : I2315aAt G
  i2315b : I2315bAt G
  i166 : I166At G
  i1441 : I1441At G
  i14neg : I14NegAt G
  u64types : U64TypesAt G
  u6struct : U6StructAt G

@[expose] def I142Res : Prop := I142.ResidualCyc ∧ I142.ResidualNonCyc

section Ys10Cat6

theorem S11Cat6Inputs.toS11Cat5Inputs
    (hR : I142Res) {G : Type} [Group G] [Finite G] (h : S11Cat6Inputs G) :
    S11Cat5Inputs G where
  i165 := h.i165
  i2315a := h.i2315a
  i2315b := h.i2315b
  i166 := h.i166
  i1441 := h.i1441
  i14neg := h.i14neg
  i142 := I142.i142At_of_E (I142.lieSemisimpleCentE_of_residuals hR.1 hR.2) G
  u64types := h.u64types
  u6struct := h.u6struct

end Ys10Cat6

end CFSG.LocalAnalysis.GLTheoremA
