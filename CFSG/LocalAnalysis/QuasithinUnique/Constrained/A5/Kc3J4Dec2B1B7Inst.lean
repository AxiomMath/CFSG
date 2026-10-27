module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1B7WLem
public import Certificates.Certificate4111

public section

namespace CFSG.QuasithinUnique.A5.B7

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT2A CFSG.Sporadic.J4.QT2.B7

@[expose] noncomputable def b7Explicit : Subgroup ↥J :=
  Subgroup.closure {x | x ∈ b7ExplicitWords.map el5}

theorem noNonHBlockAt_b7Explicit (hF : J4Basic) (h5 : ¬ 5 ^ 2 ∣ Nat.card J) :
    NoNonHBlockAt Hj b7Explicit :=
  have h := Certificates.certificate4111
  noNonHBlockAt_b7W_closure hF h5 rfl h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1
    h.2.2.2.2.2.2

end CFSG.QuasithinUnique.A5.B7
