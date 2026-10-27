module

public import CFSG.CGT.PushingUpLit.ThreeFromEightOneCore
import CFSG.CGT.PushingUpLit.BlocksCommute

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp

theorem relativeBlocksCommute (G : Type) [Group G] [Finite G] : RelativeBlocksCommute G :=
  fun _ hK _ _ hY hZ hne => distinct_blocks_commute_of_isBlockOfInX hK hY hZ hne

section Abstract

variable {G : Type} [Group G] [Finite G]

theorem exists_unique_maximalTwoLocal (hchar : IsCharacteristicPType G 2)
    (𝔛 : Set (Subgroup G)) (hconj : ∀ Z ∈ 𝔛, ∀ g : G, conjugate Z g ∈ 𝔛)
    (hX : ∀ Z ∈ 𝔛, InClassX ↥Z)
    (h81 : ∀ Z ∈ 𝔛, ∀ N : Subgroup G, N ∈ maximalTwoLocalsContaining (Z : Set G) →
      (Z.subgroupOf N).IsSubnormal)
    {X : Subgroup G} (hXm : X ∈ 𝔛) :
    ∃ M : Subgroup G, maximalTwoLocalsContaining (X : Set G) = {M} ∧
      (X.subgroupOf M).IsSubnormal :=
  exists_unique_maximalTwoLocal_of_blocksCommute (relativeBlocksCommute G) hchar 𝔛 hconj hX h81
    hXm

end Abstract

end CFSG.CGT.PushingUpLit
