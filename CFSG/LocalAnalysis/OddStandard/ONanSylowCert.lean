module

public import CFSG.LocalAnalysis.OddStandard.ONanSylowStageA
public import Certificates.Certificate6141
public import Certificates.Certificate6142
public import Certificates.Certificate6143

public section

namespace CFSG.OddStandard.ONanRec

open CFSG.CosetTable CFSG.Blueprint F2

theorem alpBound_cert : Finite AlpGrp ∧ Nat.card AlpGrp ≤ 512 :=
  Certificates.certificate6141

theorem f2Check_cert : f2Check = true :=
  Certificates.certificate6142

theorem f2QuotCheck_cert : f2QuotCheck = true :=
  Certificates.certificate6143

theorem stageA5_ON_cert :
    StageA5 NativeSporadic.ON :=
  stageA5_ON alpBound_cert

end CFSG.OddStandard.ONanRec
