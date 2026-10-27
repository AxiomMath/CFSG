module

public import CFSG.GH74.Defs
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S12.PushingUp

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne CFSG.Assembly CFSG.GH74

@[expose] def A4BlockNormalThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → KProper InCatalog G → IsCharTwoType G →
    ∀ M X : Subgroup G, IsMaximalTwoLocal M → X ≤ M → (X.subgroupOf M).IsSubnormal →
      IsShortGroup ↥X → IsNaturalAltModule ↥X 1 → maximalTwoLocalsContaining (X : Set G) = {M} →
        (X.subgroupOf M).Normal ∨ SectionalTwoRankLE G 4

end CFSG.CGT.PushingUpLit
