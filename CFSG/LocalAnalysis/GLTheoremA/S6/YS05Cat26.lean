module

public import CFSG.LocalAnalysis.GLTheoremA.S6.YS05Cat25
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267I267
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267I268

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure I267Res : Prop where
  gen : S267.S267FactGen
  p3 : S267.S267FactP3
  cls : S267.S267FactBadCls
  exc : S267.S267FactBadExc

structure I268Res : Prop where
  z1 : S267.S267FactZ1
  z3 : S267.S267FactZ3

structure S6Cat26Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i2019 : I2019At G p

section Ys05Cat26


theorem S6Cat26Inputs.toS6Cat23Inputs
    (h267 : I267Res) (h268 : I268Res) {G : Type} [Group G] [Finite G] {p : ℕ}
    (h : S6Cat26Inputs G p) : S6Cat23Inputs G p where
  i2019 := h.i2019
  i267 := S267.i267At_of_facts h267.gen h267.p3 h267.cls h267.exc G p
  i268 := S267.i268At_of_facts h268.z1 h268.z3 G p

theorem ys05_of_cat26_inputs
    (hR : D3A4Regular) (hN : D3CaseTwoOne)
    (hRes : I264bResidual2) (hS1 : I1422Lie2Fact) (h17 : I2017LRes2) (h20 : I2020Res) (h248 : I248Res) (h81 : I81Res)
    (h196 : I196Res) (h267 : I267Res) (h268 : I268Res)
    (h : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m, S6Cat26Inputs G p) : YS05 :=
  ys05_of_cat25_inputs hR hN hRes hS1 h17 h20 h248 h81 h196 fun G _ _ m hctx p hp =>
    (h G m hctx p hp).toS6Cat23Inputs h267 h268

end Ys05Cat26

end CFSG.LocalAnalysis.GLTheoremA
