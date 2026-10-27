module

public import CFSG.LargeExtraspecial.S14Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.Open

@[expose] def SmithU62LocalInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* timmesfeldPSU 6) →
      ∀ x y : G, IsConj S.z x → IsConj S.z y → x ∈ S.M → y ∈ S.M → x ∉ S.QG →
        orderOf (x * y) ∈ ({1, 2, 3, 4} : Set ℕ) ∧
          (orderOf (x * y) = 4 → IsConj S.z ((x * y) ^ 2))

@[expose] def SmithU62PathInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 10 →
    Nonempty (Mbar0 S ≃* timmesfeldPSU 6) →
      ∀ x w y : G, IsConj S.z x → IsConj S.z w → IsConj S.z y →
        Commute x S.z → Commute S.z w → Commute w y →
          ¬ Commute x w → ¬ Commute S.z y → ¬ Commute x y →
            ∃ v : G, IsConj S.z v ∧ Commute x v ∧ Commute v y

end CFSG.LargeExtraspecial.S14
