module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting
public import CFSG.Sporadic.Schreier.TitsQTCheckInputs

public section

namespace CFSG.QuasithinUnique.Lin2.TitsExam
open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.Schreier.TitsQT

@[expose] def conjFArr : Array ℕ :=
  compA 1755 (compA 1755 (compA 1755 (compA 1755 (compA 1755 conjD0 conjD1) conjD1) conjD1) conjD0)
    conjD0

@[expose] def conjFInvArr : Array ℕ := invCand 1755 conjFArr

@[expose] def conjWArr : Array ℕ := compA 1755 (compA 1755 conjFArr titsZArr) conjFInvArr

end CFSG.QuasithinUnique.Lin2.TitsExam
