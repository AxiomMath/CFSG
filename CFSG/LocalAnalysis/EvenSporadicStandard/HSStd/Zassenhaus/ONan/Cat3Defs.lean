module

public import CFSG.Blueprint.Catalog

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def ThreeA5OrS5 (C : Type*) [Group C] : Prop :=
  Nonempty (C ≃* Multiplicative (ZMod 3) × ↥(alternatingGroup (Fin 5))) ∨
    Nonempty (C ≃* Multiplicative (ZMod 3) × Equiv.Perm (Fin 5))

@[expose] def CatThreeA5 : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L → (∃ a b : L, a * b ≠ b * a) →
    Catalog L → (Nat.card L).factorization 3 = 2 →
    (∀ x : L, orderOf x = 3 → ThreeA5OrS5 ↥(centralizer ({x} : Set L))) →
    IsSporadic L .HS ∨ IsSporadic L .M23 ∨ LieModel L .PSp 2 2 2

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan
