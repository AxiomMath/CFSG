module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIICoverU62
public import Certificates.Certificate15029

public section

namespace CFSG.ComponentClassification.RankTwoHypIICover.U62

open Subgroup CFSG.ComponentClassification

theorem u62_facts : U62Facts :=
  Certificates.certificate15029

theorem hypII_of_psu_six_two
    {A : Type} [Group A] (hA : commutator A = ⊤)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel (A ⧸ center A) .PSU 6 2 1) :
    AS76b.HypII A :=
  hypII_of_psu_six_two_of_facts u62_facts hA h

end CFSG.ComponentClassification.RankTwoHypIICover.U62
