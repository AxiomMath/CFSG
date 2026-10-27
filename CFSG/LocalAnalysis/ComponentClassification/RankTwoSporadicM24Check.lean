module

public import Certificates.Certificate8045

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.M24

open CFSG.ComponentClassification.RankTwoSporadic.Cert

theorem m24_check : ∃ (xg xs : Array (Array ℕ))
    (xw : List (List ℕ)) (d : ConjData) (e0 : Array (Array ℕ)) (wit : Wit) (cl : ClosW),
    m24CheckC xg xs xw d e0 wit cl = true :=
  Certificates.certificate8045

end CFSG.ComponentClassification.RankTwoSporadic.M24
