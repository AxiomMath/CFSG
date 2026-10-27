module

public import CFSG.LocalAnalysis.GLTheoremA.S11.YS10Cat4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2All

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure S11Cat5Inputs (G : Type) [Group G] [Finite G] : Prop where
  i165 : I165At G
  i2315a : I2315aAt G
  i2315b : I2315bAt G
  i166 : I166At G
  i1441 : I1441At G
  i14neg : I14NegAt G
  i142 : I142At G
  u64types : U64TypesAt G
  u6struct : U6StructAt G

section Ys10Cat5

theorem S11Cat5Inputs.toS11Cat4Inputs
    (T : Rk2Tables) {G : Type} [Group G] [Finite G] (h : S11Cat5Inputs G) :
    S11Cat4Inputs G where
  i162 := (rk2_inputs_of_tables T G).1
  i163 := (rk2_inputs_of_tables T G).2.1
  i164 := (rk2_inputs_of_tables T G).2.2.1
  i165 := h.i165
  i2315a := h.i2315a
  i2315b := h.i2315b
  e62 := e62At_holds G
  i166 := h.i166
  eTable := (rk2_inputs_of_tables T G).2.2.2.1
  i1441 := h.i1441
  i14neg := h.i14neg
  i142 := h.i142
  rank3 := (rk2_inputs_of_tables T G).2.2.2.2.2.1
  u64types := h.u64types
  u6struct := h.u6struct
  u5case := u5CaseAt_holds G

end Ys10Cat5

end CFSG.LocalAnalysis.GLTheoremA
