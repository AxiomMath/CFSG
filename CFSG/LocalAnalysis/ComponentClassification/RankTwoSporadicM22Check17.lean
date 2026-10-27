module

public import Certificates.Certificate8042

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.M22

open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.KC.Census CFSG.Monster.B.TwoA

theorem m22_check17 :
    ∃ (sG roots : Array ℕ) (nodes : Array NodeP) (cS : ArrCertP)
      (wcs : Array (Array ArrCertP)) (pfs : Array PerfWP) (xg xs : Array ℕ) (xw : List (List ℕ)),
    m22CheckW2 true false sG roots nodes cS wcs pfs xg xs xw = true :=
  Certificates.certificate8042

theorem m22_yCensus17_cert :
    YCensus17 P0in (fun _ => False) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, h⟩ := m22_check17
  exact m22_yCensus17W2 h

end CFSG.ComponentClassification.RankTwoSporadic.M22
