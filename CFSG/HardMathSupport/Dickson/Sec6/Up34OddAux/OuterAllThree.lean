module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Assembly
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.OutLinThree
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.OutSpOrthThree
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.OutExcThree
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.OutTriThree

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Dickson.Sec6.I923
  CFSG.ComponentClassification.CatLeaf

set_option linter.unusedSectionVars false

section All


theorem noL34OuterAtThree_all : NoL34OuterAtThree (fun _ _ _ _ => True) := by
  have hO : LieOrderFormulasInput := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  exact noL34OuterAtThree_true (noL34OuterAt3_pslTwo hO) (noL34OuterAt3_pslGood hO)
    (noL34OuterAt3_psp hO) (noL34OuterAt3_psuGood hO) (noL34OuterAt3_orthOdd hO)
    (noL34OuterAt3_orthPlus hO) (noL34OuterAt3_orthMinus hO) noL34OuterAt3_d4
    noL34OuterAt3_triD4 (noL34OuterAt3_g2 hO) (noL34OuterAt3_f4 hO) (noL34OuterAt3_e6 hO)
    (noL34OuterAt3_twE6 hO) (noL34OuterAt3_e7 hO) (noL34OuterAt3_e8 hO) (noL34OuterAt3_reeG2 hO)

theorem noL34Out_three : NoL34Out 3 :=
  noL34Out_three_of_outerAtThree noL34OuterAtThree_all

end All

end CFSG.HardMathSupport.Dickson.Sec6
