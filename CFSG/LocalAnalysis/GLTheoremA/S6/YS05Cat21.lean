module

public import CFSG.LocalAnalysis.GLTheoremA.S6.YS05Cat17
public import CFSG.HardMathSupport.Dickson.BMRows.M11Rows
public import CFSG.HardMathSupport.Dickson.BMRows.M11Holds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bRes2
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3PBorMain
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3IInnerHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ITitsD4
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3IField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1422Char2Of
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD42Spec
public import CFSG.Quasithin.Recognition.CertTrialityCheckInputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure S6Cat21Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i2017Lie : I2017LieAt G
  i196 : I196At G p
  i2019 : I2019At G p
  i248 : I248At G p
  i267 : I267At G p
  i268 : I268At G p
  i81 : I81At G p
  i2020 : I2020At G p

section Ys05Cat21

theorem S6Cat21Inputs.toS6Cat17Inputs
    (hS1 : I1422Lie2Fact) {G : Type} [Group G] [Finite G] {p : ℕ}
    (h : S6Cat21Inputs G p) : S6Cat17Inputs G p where
  i2017Lie := h.i2017Lie
  i196 := h.i196
  i2019 := h.i2019
  i248 := h.i248
  i267 := h.i267
  i268 := h.i268
  i81 := h.i81
  i2020 := h.i2020
  i1422Char2 := i1422Char2_of_facts hS1 G

end Ys05Cat21

end CFSG.LocalAnalysis.GLTheoremA
