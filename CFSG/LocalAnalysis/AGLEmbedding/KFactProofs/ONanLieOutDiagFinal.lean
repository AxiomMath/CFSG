module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutDiagMain
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutPrimeMain

public section

namespace CFSG.AGLEmbedding.LieOut

open CFSG.RankThree.PartOne.FieldFix (ChevalleySubfieldNonLocalized)

section Final


theorem lieOutDich_of_inputs (hNL : ChevalleySubfieldNonLocalized) (I : LieOutInputs) :
    LieOutDich := by
  intro Y _ _ L hL hcl p hp hp5 x hx hxp hxL
  exact lieOut_diag_or_concl hNL I hL hcl hp hp5 hx hxp hxL

theorem kFactLieOutDiagLevi_of_inputs (I : LieOutInputs) (hbad : DiagLeviBad) :
    KFactLieOutDiagLevi :=
  kFactLieOutDiagLevi_of_bad (lieOutDich_of_inputs (fun τ hτ σ =>
    CFSG.SignalizerFunctorTheorem.NonLocalExc.nonLocalized_chevalley τ hτ σ) I) hbad

end Final

end CFSG.AGLEmbedding.LieOut
