module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Yardstones.M3aba7dc4b8a8.Definitions

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Aschbacher1976HigherCenter

open Subgroup CFSG
open CFSG.Yardstones.M3aba7dc4b8a8 (GF2RankFourSetting)

@[expose] def CyclicFourNotWeaklyClosed : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (z : G), GF2RankFourSetting G z →
    ∀ Z : Subgroup G, z ∈ Z → IsCyclic Z → Nat.card Z = 4 →
      ∃ g : G, conjugate Z g ≤ normalizer (Z : Set G) ∧ conjugate Z g ≠ Z

end CFSG.GF2Type.Aschbacher1976HigherCenter
