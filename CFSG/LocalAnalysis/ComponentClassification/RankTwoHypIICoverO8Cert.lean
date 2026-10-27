module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIICoverO8
public import Certificates.Certificate15019

public section

namespace CFSG.ComponentClassification.RankTwoHypIICover.O8

open Subgroup CFSG.ComponentClassification

theorem o8_pairFacts : O8PairFacts :=
  Certificates.certificate15019

theorem hypII_of_pomegaPlus_four_two
    {A : Type} [Group A] (hA : commutator A = ⊤)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel (A ⧸ center A) .POmegaPlus 4 2 1) :
    AS76b.HypII A :=
  hypII_of_pomegaPlus_four_two_of_facts o8_pairFacts hA h

end CFSG.ComponentClassification.RankTwoHypIICover.O8
