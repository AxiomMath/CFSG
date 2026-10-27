module

public import CFSG.CGT.PushingUpLit.BHS7.OmegaCStar
public import CFSG.CGT.PushingUpLit.BHS7.OmegaMaxSwap
public import CFSG.CGT.PushingUpLit.BHS7.OmegaProd
public import CFSG.CGT.PushingUpLit.BHS7.SevenFour

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6

variable {Γ : Type} [Group Γ] [Finite Γ] {G T : Subgroup Γ}

theorem seven_four_of_minCex (h : MinCex G T) : Seven4 G T :=
  seven_four_of_omegaCStar h
    (omegaCStar_of h (omegaCStarProd_of_omegaMaxSwap h (omegaMaxSwap_holds h))
      (omegaCStarAlt_of_omegaMaxSwap h (omegaMaxSwap_holds h)))

end CFSG.CGT.PushingUpLit.BHS7
