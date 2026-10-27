module

public import CFSG.GH74.GLS.Basic

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG

@[expose] def B_B2_g4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.GH74.Gen4 X → IsKGroupNative X → pPrimeCore 2 X = ⊥ →
    ∀ y : X, orderOf y = 2 → ∀ K : Subgroup X,
      IsPCompIn 2 (centralizer ({y} : Set X)) K → IsCompIn (centralizer ({y} : Set X)) K

end CFSG.GH74.GLS
