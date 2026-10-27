module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Assembly
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.OutLin
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.OutSpOrth
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.OutE6
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.OutTri

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Dickson.Sec6.I923
  CFSG.ComponentClassification.CatLeaf

set_option linter.unusedSectionVars false

section All


theorem noL34OuterAt_all (hDiagPsl : Up34DiagPsl) (hDiagPsu : Up34DiagPsu)
    (hDiagE6 : Up34DiagE6) (hDiagTwE6 : Up34DiagTwE6) (hMinus : TriD4A2Minus34) :
    NoL34OuterAt (fun _ _ _ _ => True) := by
  have hO : LieOrderFormulasInput := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  exact noL34OuterAt_true (noL34OuterAt_pslTwo hO) (noL34OuterAt_pslGood hO)
    (noL34OuterAt_pslBad hO hDiagPsl) (noL34OuterAt_psp hO) (noL34OuterAt_psuGood hO)
    (noL34OuterAt_psuBad hO hDiagPsu) (noL34OuterAt_orthOdd hO) (noL34OuterAt_orthPlus hO)
    (noL34OuterAt_orthMinus hO) (noL34OuterAt_d4_of_minus hMinus)
    (noL34OuterAt_triD4_of_minus hMinus) (noL34OuterAt_g2 hO) (noL34OuterAt_f4 hO)
    (noL34OuterAt_e6 hO hDiagE6) (noL34OuterAt_twE6 hO hDiagTwE6) (noL34OuterAt_e7 hO)
    (noL34OuterAt_e8 hO)

theorem noL34Out_ge_five (hDiagPsl : Up34DiagPsl) (hDiagPsu : Up34DiagPsu)
    (hDiagE6 : Up34DiagE6) (hDiagTwE6 : Up34DiagTwE6) (hMinus : TriD4A2Minus34) {r : ℕ}
    (hr5 : 5 ≤ r) : NoL34Out r :=
  noL34Out_of_outerAt (noL34OuterAt_all hDiagPsl hDiagPsu hDiagE6 hDiagTwE6 hMinus) hr5

end All

end CFSG.HardMathSupport.Dickson.Sec6
