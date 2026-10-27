module

public import CFSG.GH74.Generic.S3.L3Cert

public section

namespace CFSG.GH74.E2

open CFSG.Assembly.LowTwoRank

export CFSG.GH74.Generic.S3 (alpha3 alpha3_apply det_alpha3 isUni_alpha3 alpha3_scalar)

theorem rankCertified_SU3_mod_four {F : Type} [Field F] [Finite F] {q : ℕ}
    (hF : Nat.card F = q ^ 2) (hq : q % 4 = 3) :
    CFSG.GH74.Generic.RankCertified (StatedProj (StatedSU 3 q F)) 2 :=
  CFSG.GH74.Generic.S3.rankCertified_U3 hF hq

end CFSG.GH74.E2
