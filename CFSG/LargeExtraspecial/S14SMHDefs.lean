module

public import CFSG.LargeExtraspecial.S14Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.Open

@[expose] def SmithE261 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* timmesfeldPSU 6) →
      ∀ t u : G, IsConj S.z t → IsConj S.z u → t ∈ S.M → u ∈ S.M → t ∉ S.QG → u ∉ S.QG →
        orderOf (t * u) = 3 →
          ∃ N : Subgroup G, S.z ∈ N ∧ (∀ n ∈ N, Commute n t ∧ Commute n u) ∧
            Nonempty (N ≃* timmesfeldPSU 6)

end CFSG.LargeExtraspecial.S14
