module

public import CFSG.LargeExtraspecial.AS35QDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.RankThree.OrthogonalInvolutions

namespace S14

@[expose] def Asc512ThomasIndexTwoStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Setting G), S.SixHyp → S.Asc512Thomas →
    ∀ X : Subgroup S.O, X ≤ S.Mbar → (∀ m ∈ S.Mbar, ∀ x ∈ X, m * x * m⁻¹ ∈ X) →
      IsPGroup 3 X → ∀ c ∈ X, (∀ x ∈ X, c * x = x * c) → ∀ m ∈ S.Mbar, m * c = c * m

end S14

end CFSG.LargeExtraspecial
