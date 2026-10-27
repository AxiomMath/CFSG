module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.OuterAll
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.OuterAllThree
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsLinAux.DiagPsl
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsUniAux.DiagPsu
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsSp
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsOrth
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTw
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.OutTriAux.A2Minus
public import CFSG.HardMathSupport.Dickson.KD.CharP

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Dickson.Sec6.I923
  CFSG.ComponentClassification.CatLeaf CFSG.LocalAnalysis.GLTheoremA
open CFSG.Blueprint.Chevalley (Tag)

set_option linter.unusedSectionVars false

section All


theorem noL34InnAt_all (hTwoD : ∀ τ : Tag, SsExcTwoD τ) (hExc : ∀ τ : Tag, SsExcExc τ)
    (hTwE6 : NoL34InnAt FamTwE6) : NoL34InnAt (fun _ _ _ _ => True) := by
  have hO : LieOrderFormulasInput := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  exact noL34InnAt_true (noL34InnAt_pslTwo hO) (noL34InnAt_pslGood hO) (noL34InnAt_pslBad hO)
    (noL34InnAt_famPsp hO) (noL34InnAt_psuGood hO) (noL34InnAt_psuBad hO)
    (noL34InnAt_orthOdd hO) (noL34InnAt_orthPlus hO) (noL34InnAt_orthMinus hO)
    (noL34InnAt_d4 hO) (noL34InnAt_triD4 hO) (noL34InnAt_g2 hO)
    (noL34InnAt_f4 hO (hTwoD _) (hExc _)) (noL34InnAt_e6 hO (hTwoD _) (hExc _)) hTwE6
    (noL34InnAt_e7 hO (hTwoD _) (hExc _)) (noL34InnAt_e8 hO (hTwoD _) (hExc _))

theorem up34OddLeaf_of_inner (hInn3 : NoL34Inn 3) (hTwoD : ∀ τ : Tag, SsExcTwoD τ)
    (hExc : ∀ τ : Tag, SsExcExc τ) (hTwE6 : NoL34InnAt FamTwE6)
    (hDiagTwE6 : Up34DiagTwE6) : Up34OddLeaf := by
  have hO : LieOrderFormulasInput := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  refine up34OddLeaf_of_noL34 (fun r hr hr2 => ?_) (fun r hr hr2 => ?_)
  · rcases three_or_five_le_of_prime hr hr2 with rfl | h5
    · exact hInn3
    · exact noL34Inn_of_innAt (noL34InnAt_all hTwoD hExc hTwE6) h5
  · rcases three_or_five_le_of_prime hr hr2 with rfl | h5
    · exact noL34Out_three
    · exact noL34Out_ge_five (up34DiagPsl_of_hO hO) (up34DiagPsu_of_lieOrderFormulas hO)
        (up34DiagE6_holds_of (hTwoD _) (hExc _)) hDiagTwE6 triD4A2Minus34_holds h5

theorem up34OddLeaf_of_kdCharP (hTwoD : ∀ τ : Tag, SsExcTwoD τ) (hExc : ∀ τ : Tag, SsExcExc τ)
    (hTwE6 : NoL34InnAt FamTwE6) (hDiagTwE6 : Up34DiagTwE6) : Up34OddLeaf :=
  up34OddLeaf_of_inner
    (noL34Inn_three_of_kdCharP (CFSG.HardMathSupport.Dickson.KD.kdCharP_holds Nat.prime_three
      (by norm_num)))
    hTwoD hExc hTwE6 hDiagTwE6

theorem up34OddLeaf_holds : Up34OddLeaf := by
  have hO : LieOrderFormulasInput := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  exact up34OddLeaf_of_kdCharP ssExcTwoD_holds ssExcExc_holds (noL34InnAt_twE6 hO)
    (up34DiagTwE6_holds hO)

end All

end CFSG.HardMathSupport.Dickson.Sec6
