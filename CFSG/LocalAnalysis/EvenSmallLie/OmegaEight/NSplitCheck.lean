module

public import Certificates.Certificate3850

public section

namespace CFSG.EvenSmallLie.OmegaEight.NSplit

open CFSG.EvenSmallLie.OmegaEight.Stage1


theorem nsGenCheck_plus : nsGenCheck .plus = true := Certificates.certificate3850.1

theorem nsGenCheck_minus : nsGenCheck .minus = true := Certificates.certificate3850.2.1

theorem nsRelCheck_plus : nsRelCheck .plus = true := Certificates.certificate3850.2.2.1

theorem nsRelCheck_minus : nsRelCheck .minus = true := Certificates.certificate3850.2.2.2.1

theorem nsCosetCheck_true : Finite (CFSG.CosetTable.PG 7 relPG) ∧
    Nat.card (CFSG.CosetTable.PG 7 relPG) ≤ 1451520 :=
  Certificates.certificate3850.2.2.2.2.1

theorem nsChainCheck_plus : nsChainCheck .plus = true :=
    Certificates.certificate3850.2.2.2.2.2.1

theorem nsChainCheck_minus : nsChainCheck .minus = true :=
    Certificates.certificate3850.2.2.2.2.2.2.1

theorem nsGamCheck_plus : nsGamCheck .plus = true :=
    Certificates.certificate3850.2.2.2.2.2.2.2.1

theorem nsGamCheck_minus : nsGamCheck .minus = true :=
    Certificates.certificate3850.2.2.2.2.2.2.2.2.1

theorem nsH1Check_plus : nsH1Check .plus = true :=
    Certificates.certificate3850.2.2.2.2.2.2.2.2.2.1

theorem nsH1Check_minus : nsH1Check .minus = true :=
    Certificates.certificate3850.2.2.2.2.2.2.2.2.2.2.1

theorem nsSplitCheck_plus :
    ∃ Y : Array ℕ, splitTest .plus (29 * nM .plus) (fmMat .plus) (iotaMat .plus) Y = true :=
  Certificates.certificate3850.2.2.2.2.2.2.2.2.2.2.2.1

theorem nsSplitCheck_minus :
    ∃ Y : Array ℕ, splitTest .minus (29 * nM .minus) (fmMat .minus) (iotaMat .minus) Y = true :=
  Certificates.certificate3850.2.2.2.2.2.2.2.2.2.2.2.2

end CFSG.EvenSmallLie.OmegaEight.NSplit
