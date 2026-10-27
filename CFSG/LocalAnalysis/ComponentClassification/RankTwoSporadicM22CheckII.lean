module

public import Certificates.Certificate8043

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.M22

open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.KC.Census CFSG.Monster.B.TwoA

theorem m22_checkII :
    ∃ (sG roots : Array ℕ) (nodes : Array NodeP) (cS : ArrCertP)
      (wcs : Array (Array ArrCertP)) (xg xs : Array ℕ) (xw : List (List ℕ)),
    m22CheckW false true sG roots nodes cS wcs xg xs xw = true :=
  Certificates.certificate8043

theorem m22_yCensusII_cert :
    YCensus P0in (· ≤ P0in) := by
  obtain ⟨_, _, _, _, _, _, _, _, h⟩ := m22_checkII
  exact m22_yCensusIIW h

end CFSG.ComponentClassification.RankTwoSporadic.M22
