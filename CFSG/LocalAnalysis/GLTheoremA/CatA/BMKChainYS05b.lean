module

public import CFSG.LocalAnalysis.GLTheoremA.S6.YS05Cat14
public import CFSG.LocalAnalysis.GLTheoremA.S6.YS05Cat12
public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMKChainYS05a
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04D3Bundle

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Dickson.BMRows (I1416QSporSK i1416At_of_sporK)

section BMKChainYS05b


theorem S6Cat13Inputs.toS6Cat12InputsK
    (hS : YS05SporTablesK) {G : Type} [Group G] [Finite G] {p : ℕ}
    (h : S6Cat13Inputs G p) : S6Cat12Inputs G p where
  charThree := h.charThree
  i196 := h.i196
  i2019 := h.i2019
  i248 := h.i248
  i267 := h.i267
  i268 := h.i268
  i81 := h.i81
  i2020 := h.i2020
  i1422Char2 := h.i1422Char2
  i2017 := i2017At_of_lieK h.i2017Lie hS.i1422
  i264ChevTwo := h.i264ChevTwo

theorem ys05_of_cat12K
    (hS : YS05SporTablesK)
    (h : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m →
      ∀ p ∈ Mu G m, S6Cat12Inputs G p) : YS05 :=
  ys05_of_cat9K hS fun G _ _ m hctx p hp => (h G m hctx p hp).toS6Cat9Inputs

theorem ys05_of_cat13K
    (hS : YS05SporTablesK)
    (h : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m →
      ∀ p ∈ Mu G m, S6Cat13Inputs G p) : YS05 :=
  ys05_of_cat12K hS fun G _ _ m hctx p hp => (h G m hctx p hp).toS6Cat12InputsK hS

theorem ys05_of_cat14K
    (hS : YS05SporTablesK) (hD3 : D3Facts)
    (h : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m →
      ∀ p ∈ Mu G m, S6Cat14Inputs G p) : YS05 :=
  ys05_of_cat13K hS fun G _ _ m hctx p hp =>
    (h G m hctx p hp).toS6Cat13Inputs (noTrialityCharThreeAt_of_d3Facts hD3 hctx)

end BMKChainYS05b

end CFSG.LocalAnalysis.GLTheoremA
