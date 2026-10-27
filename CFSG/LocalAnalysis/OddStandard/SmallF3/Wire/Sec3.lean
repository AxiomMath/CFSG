module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGClosureAt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGSchurU43
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.OutQ
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2GenMain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClEightP
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClSeven
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L311Final
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GCommute
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GM3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GPocket
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXF0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXKA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXKB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3W12Leaf
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4S47RFinal

public section

namespace CFSG.OddStandard.SmallF3

open CFSG.OddStandard.SmallF3.Omega

theorem ys09asm_sec3 (hGA : CFSG.Open.GriessAllModelsStatement) (hCorIII : Asc82CorIII)
    (hW12 : Asc82Walter12L2) (hNCP : Asc82NonCommuteNonPocketed)
    (hCoreF0 : Asc82CoreF0) (hFactO3Cent : Asc82FactO3Cent) (hFactCent3 : Asc82FactCent3)
    (hCoreKGA : Asc82CoreKGA) (hCoreKGB : Asc82CoreKGB) (hStd : Asc82StandardInput)
    (hOmPlusAut : Asc82OmegaPlusAutInvolutions) :
    Asc82Sec3Results ∧ Asc82Lemma34a ∧ AschOmega7 ∧ AschOmega8Plus ∧ AschOmega8Minus := by
  have hThm2Q := asc82Thm2Q_holds
  have hSchurU43 := fg_asc82SchurU43 hGA
  have hFactNoncentralFixed := asc82FactNoncentralFixed_of_core hCoreF0
  have hCommuteStep := asc82CommuteStep_of_facts hFactO3Cent hFactCent3
    (l34g_schurOdd3_of_griess hGA) hFactNoncentralFixed
  have hCommutingPocket := asc82CommutingPocket_of_facts hThm2Q hCommuteStep hSchurU43
    hCorIII hFactNoncentralFixed (asc82FactPocketComp_of_core hCoreKGA)
    (asc82FactPocketLift_of_core hCoreKGB)
  have h34c := asc82Lemma34c_of_inputs_q8 hThm2Q hCommuteStep hCommutingPocket
    asc82NoQ8InL2_holds asc82OddCoreCentralizerQ8_holds hSchurU43
  have hPocketExists := asc82PocketExists_of_schur hSchurU43
  have h35 := asc82Lemma35_of_34c h34c
  have h36 := asc82Lemma36_of_35 h35 hPocketExists
  have h38 := asc82Lemma38_of_named_inputs hThm2Q hCommuteStep hCommutingPocket hSchurU43
  have h33 := asc82Lemma33_of_walter12F (asc82Walter12F_of_L2 h36 hW12) hNCP hPocketExists h34c hStd
  have h34a := asc82Lemma34a_of_inputs hThm2Q hCommuteStep
  have hOuter := asc82OmegaPlusOuter_of_autInvolutions hOmPlusAut
  have hCl := asc82OmegaPlusClosure_holds hOmPlusAut
  have hGen := asc82OmegaPlusGen_holds
  have h311 := asc82Lemma311_of_inputs (asc82Lemma33F_of_lemma33 h33) h34a h34c h36
    (asc82Lemma39_of_36 h36) (asc82OmegaPlusInner_of_projInner asc82OmegaPlusProjInner_holds)
    hOuter asc82OmegaPlusPocketedConj_holds asc82OmegaPlusPocketLift_holds hCl
    asc82OmegaPlusCStar hPocketExists hGen
  have h37 := asc82Lemma37_of_parts h36 (asc82Lemma37F_of_35_36 h35 h36) fg_closureAt_o5
    fg_closureAt_o6p fg_closureAt_o6m (fg_closureAt_twoU43 hGA) asc82ClosureAt_seven h38 h311
  have h3 : Asc82Sec3Results := ⟨h33, h36, h37, h38, asc82Lemma39_of_36 h36, h311⟩
  exact ⟨h3, h34a, aschOmega7_of_sec3 h3,
    aschOmega8Plus_of_remaining_inputs hThm2Q hCommuteStep hCommutingPocket hSchurU43
      (asc82StandardInputF_of_standardInput hStd) hOuter hCl hGen,
    aschOmega8Minus_of_named_inputs hThm2Q hCommuteStep hCommutingPocket hSchurU43⟩

end CFSG.OddStandard.SmallF3
