module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q22RowsAsm
public import CFSG.ClassicalInvolution.Q3.Q3OTShape
public import CFSG.ClassicalInvolution.Q3.Q3OTSqAll
public import CFSG.ClassicalInvolution.Q3.Q3OTOuterAll
public import CFSG.ClassicalInvolution.Q3.Q3OTSmallSp
public import CFSG.ClassicalInvolution.Q3.Q3OTSmallSU
public import CFSG.ClassicalInvolution.Q3.Q3OTSmallSUClass
public import CFSG.ClassicalInvolution.Q3.Q3OTSmallExc
public import CFSG.ClassicalInvolution.Asc77.AscC25W13
public import CFSG.ClassicalInvolution.Asc77.AscS22F
public import CFSG.ClassicalInvolution.Asc77.AscS22G
public import CFSG.ClassicalInvolution.Asc77.AscT7QFinal
public import CFSG.ClassicalInvolution.Asc77.AscT7TWire
public import CFSG.ClassicalInvolution.Asc77.AscT7U10
public import CFSG.ClassicalInvolution.Q3.Q3CPOmega
public import CFSG.ClassicalInvolution.Q3.Q3T7P25A05
public import CFSG.ClassicalInvolution.Q3.Q3T7Stmt
public import CFSG.ClassicalInvolution.Q3.Q3T8P1Seven
public import CFSG.ClassicalInvolution.Q3.Q3T8Std8
public import CFSG.ClassicalInvolution.Q3.Q3ZFraStd
public import CFSG.Sporadic.J4.QT2LocProof

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Generic


theorem twinPairShape3_proved : TwinPairShape3 := by
  intro t n ht hadm H _ _ ψ R R' x x' hpair
  exact Q3OT.twinPairOn_shape3 ht hadm ψ hpair

theorem twinOuterRows3_proved : TwinOuterRows3 where
  psp := Q3OT.twinOuterAlpha3_psp
  psl := Q3OT.twinOuterAlpha3_psl
  psu := Q3OT.twinOuterAlpha3_psu
  odd := Q3OT.twinOuterAlpha3_odd'
  plus := Q3OT.twinOuterAlpha3_plus'
  minus := Q3OT.twinOuterAlpha3_minus'

theorem twinOuterAlphaAll3_proved : TwinOuterAlphaAll3 :=
  twinOuterAlphaAll3_of_rows twinPairShape3_proved twinOuterRows3_proved
    (fun _ h => Q3OT.twinOuterAlpha3_g2 h) (fun _ h => Q3OT.twinOuterAlpha3_trialityD4 h)

theorem twinSqRows3_proved : TwinSqRows3 where
  psp := Q3OT.twinSqAlpha3_psp
  psl := Q3OT.twinSqAlpha3_psl
  psu := Q3OT.twinSqAlpha3_psu
  odd := Q3OT.twinSqAlpha3_odd'
  plus := Q3OT.twinSqAlpha3_plus'
  minus := Q3OT.twinSqAlpha3_minus'

theorem twinSqAlphaAll3_proved : TwinSqAlphaAll3 :=
  twinSqAlphaAll3_of_rows twinPairShape3_proved twinSqRows3_proved
    (fun _ h => Q3OT.twinSqAlpha3_g2 h) (fun _ h => Q3OT.twinSqAlpha3_trialityD4 h)

end CFSG.ClassicalInvolution.Q3.Q3T7
