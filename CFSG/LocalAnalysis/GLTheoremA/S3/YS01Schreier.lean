module

public import CFSG.LocalAnalysis.GLTheoremA.S3.YS01Reduction
public import CFSG.LocalAnalysis.GLTheoremA.S4.LBalanceBridge
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3VMain
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal


theorem ys01_of_remaining
    (hKM : KMUsedAt)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m,
      I1135At G p ∧ ChevClosureAt G p ∧ ChevUniqueAt G p ∧ ChevInnerAt G p ∧ I65At G p ∧
        I76At G p ∧ ChevRank3At G p ∧ I112L227At G ∧ L227DataAt G ∧ L227PumpAt G) : YS01 :=
  have hS := CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog
    CFSG.RankThree.PartOne.SPOR.schreierFor_catalog
  ys01_of_inputs fun G _ _ m hctx p hp =>
    let h := hin G m hctx p hp
    { km := hKM
      lBalance := lBalanceAt_of_catalogueSchreier hS hp.1.1
      input18_3_4 := CFSG.HardMathSupport.Solomon.Coordinator.input18_3_4_of_schreier hS
      input18_3_12 := CFSG.HardMathSupport.Solomon.Coordinator.input18_3_12_of_schreier hS
      i1135 := h.1
      chevClosure := h.2.1
      chevUnique := h.2.2.1
      chevInner := h.2.2.2.1
      i65 := h.2.2.2.2.1
      i76 := h.2.2.2.2.2.1
      chevRank3 := h.2.2.2.2.2.2.1
      i112L227 := h.2.2.2.2.2.2.2.1
      l227Data := h.2.2.2.2.2.2.2.2.1
      l227Pump := h.2.2.2.2.2.2.2.2.2 }

end CFSG.LocalAnalysis.GLTheoremA
