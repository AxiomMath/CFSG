module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AB1E
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL41Syl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL41E8
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AY11F
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL41U
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AM13C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ACtxIdx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ATauD
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ACtxOuter
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ACtxCentreB

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

theorem ctxOfLemma4_1_holds : CtxOfLemma4_1Stmt :=
  ctxOfLemma4_1_of_steps ctxLModel_holds ctxIdx_holds ctxTau_holds ctxOuter_holds
    ctxCentre_holds ctxNorm_holds

theorem lemma4_1_of_open_steps (s10 : L41RAbelianStmt) (s14 : L41QStmt) (s15 : L41Q1Stmt)
    (s16 : L41CentQ1Stmt) (s17 : L41Q1ElemStmt) (s18 : L41FinalStmt) : Lemma4_1Stmt :=
  lemma4_1_of_steps l41_basic_holds l41_sylow_holds l41_fusion_holds l41_normalizer_holds
    l41_p2_holds l41_e8_holds l41_nbar_holds l41_r_holds l41_hs29_holds s10 l41_y_holds
    l41_uniqueY_holds l41_mbasic_holds s14 s15 s16 s17 s18

end CFSG.OddStandard.SmallF3.HarrisU33
