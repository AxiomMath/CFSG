module

public import CFSG.LocalAnalysis.GLTheoremA.S6.YS05Cat16
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Shared
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3IInnerHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ITitsD4
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3IField
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeALocalBase
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeL1Orb
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1ThreeAFinal
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24LeafShape
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMDownMGmat
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Glue
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpInputs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIPComp
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Alt
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporFi24
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporHe7
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop115b
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupEven
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVDefs
public import CFSG.RankThree.ThinCatalog.EvenLinearTwoLocal
public import Certificates.Certificate17632Base
public import Certificates.Data.TabCo1ThreeE

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure S6Cat17Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i2017Lie : I2017LieAt G
  i196 : I196At G p
  i2019 : I2019At G p
  i248 : I248At G p
  i267 : I267At G p
  i268 : I268At G p
  i81 : I81At G p
  i2020 : I2020At G p
  i1422Char2 : I1422Char2At G

section Ys05Cat17

theorem S6Cat17Inputs.toS6Cat14Inputs
    (hR : I264bResidual) {G : Type} [Group G] [Finite G] {p : ℕ}
    (h : S6Cat17Inputs G p) : S6Cat14Inputs G p where
  i2017Lie := h.i2017Lie
  i196 := h.i196
  i2019 := h.i2019
  i248 := h.i248
  i267 := h.i267
  i268 := h.i268
  i81 := h.i81
  i2020 := h.i2020
  i1422Char2 := h.i1422Char2
  i264ChevTwo := i264ChevTwoAt_of_residual (fun hp Y _ _ => lBalanceAt_holds Y p hp) hR

end Ys05Cat17

end CFSG.LocalAnalysis.GLTheoremA
