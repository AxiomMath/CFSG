module

public import CFSG.LocalAnalysis.GLTheoremA.S8.YS06Cat8
public import CFSG.LocalAnalysis.GLTheoremA.CatB.TimmU7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMKBridge1415
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I66At
public import CFSG.LocalAnalysis.GLTheoremA.CatB.No5Pumpup
public import CFSG.LocalAnalysis.GLTheoremA.S8.YS06Cat5
public import CFSG.LocalAnalysis.GLTheoremA.S8.YS06Cat6

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Dickson.BMRows (I1416QSporSK i1416At_of_sporK)

section BMKChainYS06


structure YS06SporTablesNoNine : Prop where
  i66 : I66RealS
  bm : CFSG.HardMathSupport.Solomon.Coordinator.NoOrderSixtyFiveBM

theorem S8Cat7Inputs.toS8Cat6InputsK
    (hS : YS06SporTablesNoNine) {G : Type} [Group G] [Finite G] {p : ℕ}
    (h : S8Cat7Inputs G p) : S8Cat6Inputs G p where
  i66 := i66At_of_real hS.i66
  i1017 := h.i1017
  i1016Row := h.i1016Row
  i301A := h.i301A
  timmesfeld := h.timmesfeld
  no5Pumpup := no5PumpupAt_of_BM hS.bm
  in84_i1430 := h.in84_i1430
  in84_i106 := h.in84_i106
  in84_i1431 := h.in84_i1431
  in8910_cfgI := h.in8910_cfgI
  in8910_i301B := h.in8910_i301B
  in8910_i1420 := h.in8910_i1420
  in8910_i1431 := h.in8910_i1431
  in8910_i2016 := h.in8910_i2016
  in8910_i1432 := h.in8910_i1432

theorem S8Cat6Inputs.toS8Cat5InputsK
    (hS : I1415NineSporSK) {G : Type} [Group G] [Finite G] {p : ℕ}
    (h : S8Cat6Inputs G p) : S8Cat5Inputs G p where
  i66 := h.i66
  i1017 := h.i1017
  i1016Row := h.i1016Row
  i301A := h.i301A
  timmesfeld := h.timmesfeld
  no5Pumpup := h.no5Pumpup
  in83_i1415 := l83_i1415NineAt_of_sporK hS G
  in84_i1430 := h.in84_i1430
  in84_i106 := h.in84_i106
  in84_i1431 := h.in84_i1431
  in8910_cfgI := h.in8910_cfgI
  in8910_i301B := h.in8910_i301B
  in8910_i1420 := h.in8910_i1420
  in8910_i1431 := h.in8910_i1431
  in8910_i2016 := h.in8910_i2016
  in8910_i1432 := h.in8910_i1432

theorem ys06_of_cat6K
    (hS : I1415NineSporSK)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m, S8Cat6Inputs G p) : YS06 :=
  ys06_of_cat5_inputs fun G _ _ m hctx p hp => (hin G m hctx p hp).toS8Cat5InputsK hS

theorem ys06_of_cat7K
    (hN : I1415NineSporSK) (hS : YS06SporTablesNoNine)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m, S8Cat7Inputs G p) : YS06 :=
  ys06_of_cat6K hN fun G _ _ m hctx p hp => (hin G m hctx p hp).toS8Cat6InputsK hS

theorem ys06_of_cat8K
    (hN : I1415NineSporSK) (hS : YS06SporTablesNoNine) (hT : Timm.TimmesfeldUnitaryAt)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m, S8Cat8Inputs G p) : YS06 :=
  ys06_of_cat7K hN hS fun G _ _ m hctx p hp => (hin G m hctx p hp).toS8Cat7Inputs hT

theorem ys06_of_cat9K
    (hN : I1415NineSporSK) (hS : YS06SporTablesNoNine)
    (hI : Timm.UnitaryPoint.UnitaryPointIdentification)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m, S8Cat8Inputs G p) : YS06 :=
  ys06_of_cat8K hN hS (Timm.UnitaryPoint.timmesfeldUnitaryAt_of_identification hI) hin

end BMKChainYS06

end CFSG.LocalAnalysis.GLTheoremA
