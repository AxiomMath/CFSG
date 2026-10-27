module

public import CFSG.LocalAnalysis.GLTheoremA.S6.YS05Cat9
public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMKBridge1415
public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMKBridge7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMKBridge22
public import CFSG.LocalAnalysis.GLTheoremA.S6.YS05Cat7
public import CFSG.LocalAnalysis.GLTheoremA.S6.YS05Cat8

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Dickson.BMRows (I1416QSporSK i1416At_of_sporK)

section BMKChainYS05a


structure YS05SporTablesK : Prop where
  i1416 : I1416QSporSK
  i1415 : I1415SporSK
  i1415Nine : I1415NineSporSK
  i1415Seven : I1415SevenSporSK
  i1422 : I1422SporSK

theorem S6Cat8Inputs.toS6Cat7InputsK
    (hS : I1416QSporSK) {G : Type} [Group G] [Finite G] {p : ℕ}
    (h : S6Cat8Inputs G p) : S6Cat7Inputs G p where
  i1416 := i1416At_of_sporK hS G p
  i71i117 := h.i71i117
  i196 := h.i196
  i2019 := h.i2019
  i248 := h.i248
  i267 := h.i267
  i268 := h.i268
  i81 := h.i81
  i2020 := h.i2020
  i1415 := h.i1415
  i1415Nine := h.i1415Nine
  i1415Seven := h.i1415Seven
  i1422 := h.i1422
  i2017 := h.i2017
  i264ChevTwo := h.i264ChevTwo

theorem S6Cat9Inputs.toS6Cat8InputsK
    (hS : YS05SporTablesK) {G : Type} [Group G] [Finite G] {p : ℕ}
    (h : S6Cat9Inputs G p) : S6Cat8Inputs G p where
  i71i117 := h.i71i117
  i196 := h.i196
  i2019 := h.i2019
  i248 := h.i248
  i267 := h.i267
  i268 := h.i268
  i81 := h.i81
  i2020 := h.i2020
  i1415 := i1415At_of_sporK hS.i1415 G p
  i1415Nine := i1415NineAt_of_sporK hS.i1415Nine G
  i1415Seven := i1415Seven_of_sporK hS.i1415Seven G
  i1422 := i1422At_of_sporK hS.i1422 G h.i1422Char2
  i2017 := h.i2017
  i264ChevTwo := h.i264ChevTwo

theorem ys05_of_cat8K
    (hS : I1416QSporSK)
    (h : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m →
      ∀ p ∈ Mu G m, S6Cat8Inputs G p) : YS05 :=
  ys05_of_cat7_inputs fun G _ _ m hctx p hp => (h G m hctx p hp).toS6Cat7InputsK hS

theorem ys05_of_cat9K
    (hS : YS05SporTablesK)
    (h : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m →
      ∀ p ∈ Mu G m, S6Cat9Inputs G p) : YS05 :=
  ys05_of_cat8K hS.i1416 fun G _ _ m hctx p hp => (h G m hctx p hp).toS6Cat8InputsK hS

end BMKChainYS05a

end CFSG.LocalAnalysis.GLTheoremA
