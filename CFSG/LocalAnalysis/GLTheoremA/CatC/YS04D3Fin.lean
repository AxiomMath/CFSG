module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04D3Main
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04D3Six
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04D3Four
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04D3Split

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Yardstones.Md0ec50421ce4

section Certs


theorem noTrialityCharThreeAt_of_facts
    {G : Type} [Group G] [Finite G] {m : ℕ} (hctx : ThmACtx G m)
    (hC : D3TrialityCentRank) (hI : D3InnerInvolution) (hF : D3FieldInvolution)
    (hP : D3FixedPointFree) : NoTrialityCharThreeAt G :=
  noTrialityCharThreeAt_aux CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
    CFSG.HardMathSupport.Timmesfeld.Coordinator.tables112_holds
    CFSG.HardMathSupport.Timmesfeld.Tables.Census.tableL2_unconditional
    CFSG.HardMathSupport.Solomon.Coordinator.tables112Types_holds hctx.1.simple hctx.1.kProper
    d3AbelianSix_holds d3TwoLocalFour_holds hC (d3TwoLocalTriality_of hI hF hP)

theorem ys04_of_facts
    (hC : D3TrialityCentRank) (hI : D3InnerInvolution) (hF : D3FieldInvolution)
    (hP : D3FixedPointFree) : YS04 :=
  ys04_of_charThree fun _ _ _ _ hctx => noTrialityCharThreeAt_of_facts hctx hC hI hF hP

end Certs

end CFSG.LocalAnalysis.GLTheoremA
