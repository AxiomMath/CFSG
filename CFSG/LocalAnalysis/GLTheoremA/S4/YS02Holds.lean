module

public import CFSG.LocalAnalysis.GLTheoremA.S4.YS02Reduction
public import CFSG.LocalAnalysis.GLTheoremA.S4.LBalanceBridge
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Main
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1131Holds
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1122Holds
public import CFSG.RankThree.PartOne.SPOR.Final
public import CFSG.RankThree.PartOne.TCB.Final

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB


theorem ys02_of_i1132_i1412
    (h1132 : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m,
      I1132UsedAt G p)
    (h1412 : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m,
      I1412UsedAt G p)
    (hM : ∀ p : ℕ, p.Prime → p ≠ 2 → ListedMultiplierBound p) (hH : HatOddMultiplierBound) :
    YS02 :=
  have hS := CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog
    CFSG.RankThree.PartOne.SPOR.schreierFor_catalog
  ys02_of_inputs fun G _ _ m hctx p hp =>
    ⟨CFSG.HardMathSupport.Solomon.Coordinator.input18_3_4_of_schreier hS,
      i1131At_holds hctx.1.simple hctx.1.nonabelian hctx.1.kProper hp.1.1 hp.1.2.1,
      i1122IsoAt_holds hctx.1.simple hctx.1.nonabelian hctx.1.kProper hp.1.1 hp.1.2.1,
      h1132 G m hctx p hp, h1412 G m hctx p hp,
      lBalanceAt_of_catalogueSchreier hS hp.1.1, hM p hp.1.1 hp.1.2.1, hH⟩

end CFSG.LocalAnalysis.GLTheoremA
