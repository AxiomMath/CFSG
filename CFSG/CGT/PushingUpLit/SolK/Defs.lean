module

import CFSG.GroupTheory.PCore.Transport
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S12.PushingUp

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.RankThree.PartOne

theorem pCoreOf_eq_map (p : ℕ) {G : Type*} [Group G] (H : Subgroup G) :
    CFSG.Assembly.pCoreOf p H = (CFSG.pCore p ↥H).map H.subtype :=
  CFSG.Assembly.pCoreOf_eq_map_pCore p H

structure SolHyp (G : Type) [Group G] [Finite G] (M X : Subgroup G) (n : ℕ) : Prop where
  simple : IsSimpleGroup G
  charTwo : CFSG.Assembly.IsCharTwoType G
  maxLocal : CFSG.IsMaximalTwoLocal M
  le : X ≤ M
  normal : (X.subgroupOf M).Normal
  unique : CFSG.maximalTwoLocalsContaining (X : Set G) = {M}
  short : IsShortGroup ↥X
  nat : IsNaturalAltModule ↥X n
  two_le : 2 ≤ n

end CFSG.CGT.PushingUpLit.SolK
