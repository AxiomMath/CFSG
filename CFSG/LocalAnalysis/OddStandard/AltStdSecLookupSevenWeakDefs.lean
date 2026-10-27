module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.Blueprint

@[expose] def WeakA7Lookup : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (W : Subgroup A) [W.Normal], IsSimpleGroup W →
    (∃ x y : W, x * y ≠ y * x) → centralizer (W : Set A) = ⊥ → Catalog W →
    ∀ a : A, orderOf a = 2 → ∀ B : Subgroup A, B ≤ W →
      CFSG.Assembly.IsComponentOf B (centralizer ({a} : Set A)) →
      Nonempty (B ≃* alternatingGroup (Fin 7)) →
        ∃ N : ℕ, Nonempty (W ≃* alternatingGroup (Fin N))

end CFSG.OddStandard.AltStdSec
