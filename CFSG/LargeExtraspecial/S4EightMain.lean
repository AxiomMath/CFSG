module

public import CFSG.LargeExtraspecial.S4SevenN0

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem isPGroup_Nbar_of_eq (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (hNN0 : Nbar S g t = N0bar S g t) : IsPGroup 2 (Nbar S g t) := by
  rw [hNN0]
  exact isPGroup_N0bar H ht

end CFSG.LargeExtraspecial.S4
