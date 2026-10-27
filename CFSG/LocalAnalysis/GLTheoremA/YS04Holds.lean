module

public import CFSG.LocalAnalysis.GLTheoremA.YS04Reduction
public import CFSG.LocalAnalysis.GLTheoremA.S4.I1122Iso
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Main
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1131Holds
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1122Holds
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I64
public import CFSG.RankThree.PartOne.SPOR.Final
public import CFSG.RankThree.PartOne.TCB.Final

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB


theorem ys04_of_remaining
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m,
      I1411At G p ∧ I113UsedAt G p ∧ I71UsedAt G p ∧ I2611UsedAt G p) : YS04 := ys04_of_inputs fun G _ _ m hctx p hp =>
    haveI := hctx.1.simple
    let h := hin G m hctx p hp
    have h1131 := i1131At_holds hctx.1.simple hctx.1.nonabelian hctx.1.kProper hp.1.1 hp.1.2.1
    ⟨CFSG.HardMathSupport.Solomon.Coordinator.input18_3_4_of_schreier
        (CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog
          CFSG.RankThree.PartOne.SPOR.schreierFor_catalog),
      h1131, h.1,
      i1122At_of_iso h1131
        (i1122IsoAt_holds hctx.1.simple hctx.1.nonabelian hctx.1.kProper hp.1.1 hp.1.2.1),
      h.2.1, h.2.2.1, h.2.2.2, i64UsedAt_holds hctx.1.nonabelian hctx.1.kProper hp.1.1 hp.1.2.1⟩

end CFSG.LocalAnalysis.GLTheoremA
