module

public import Certificates.Certificate15003

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.J3

open CFSG.KC.Census

theorem j3_check :
    ∃ (si xe : Array ℕ) (ws : List (List ℕ)) (d : ConjDataP), j3CheckW si xe ws d = true :=
  Certificates.certificate15003

end CFSG.ComponentClassification.RankTwoSporadic.J3
