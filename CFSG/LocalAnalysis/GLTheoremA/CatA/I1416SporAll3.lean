module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporAll
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFi24
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporJ4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporCo1Seven
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFi24Seven
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporCo1Five
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFi23FiveRow

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.I1416Rows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def I1416SporResidual3 : Prop :=
  (∀ p, I1416SporRow .B p) ∧ (∀ p, I1416SporRow .M p) ∧ I1416SporRow .Co1 3 ∧
    I1416SporRow .Fi24Prime 5 ∧ I1416SporRow .Fi23 5

theorem i1416TwoSporS_of_residual3
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    (hres : I1416SporResidual3) : I1416TwoSporS := by
  obtain ⟨hB, hM, hCo13, hF5, hFi235⟩ := hres
  exact i1416TwoSporS_of_residual2 hOut hbr hOrd hb ⟨hB, hM, hCo13,
    CFSG.HardMathSupport.Dickson.I271.TabCo1.row_Co1_five hOut hbr hb,
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1S.row_Co1_seven hOut hbr hb,
    CFSG.HardMathSupport.Dickson.I271.TabFi24.row_Fi24_three hOut hbr hb, hF5,
    CFSG.HardMathSupport.Dickson.I271.Fi7.row_Fi24_seven hOut hbr hb,
    CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.row_J4_three hOut hbr hb, hFi235⟩

@[expose] def I1416SporResidual4 : Prop :=
  (∀ p, I1416SporRow .B p) ∧ (∀ p, I1416SporRow .M p) ∧ I1416SporRow .Co1 3 ∧
    I1416SporRow .Fi24Prime 5

theorem i1416TwoSporS_of_residual4
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    (hres : I1416SporResidual4) : I1416TwoSporS := by
  obtain ⟨hB, hM, hCo13, hF5⟩ := hres
  exact i1416TwoSporS_of_residual3 hOut hbr hOrd hb ⟨hB, hM, hCo13, hF5,
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Five.row_Fi23_five hOut hbr hb⟩

end CFSG.LocalAnalysis.GLTheoremA.I1416Rows
