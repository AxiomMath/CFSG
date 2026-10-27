module

public import Certificates.Certificate15102

public section

namespace CFSG.ComponentClassification.GMS78.RuPi7

open CFSG.CosetTable

abbrev Pi7 : Type := PG 7 pi7Rels

theorem card_pi7_le :
    Finite Pi7 ∧ Nat.card Pi7 ≤ 145926144000 :=
  Certificates.certificate15102

end CFSG.ComponentClassification.GMS78.RuPi7
