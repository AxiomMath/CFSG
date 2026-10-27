module

public import Certificates.Certificate4029

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

theorem pent_reps_complete
    (p : Row) (v : ↥J) (h : PentCand p v) :
    ∃ k ∈ X0Sub, ∃ q ∈ {q : Row | ∃ w ∈ d4Reps.toList, q = toRow w.toVec}, p = k • q :=
  Certificates.certificate4029.1 p v h

end CFSG.QuasithinUnique.A5
