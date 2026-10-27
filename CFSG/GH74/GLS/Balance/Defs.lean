module

public import CFSG.GH74.GLS.Basic

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS
open scoped MatrixGroups

@[expose] def IsSolvTwoCompSL23 (Y : Type*) [Group Y] (V : Subgroup Y) : Prop :=
  ∃ W : Subgroup (Y ⧸ pPrimeCore 2 Y), W.IsSubnormal ∧ Nonempty (↥W ≃* SL(2, ZMod 3)) ∧
    V = W.comap (QuotientGroup.mk' (pPrimeCore 2 Y))

@[expose] def IsSolvTwoCompSL23In {G : Type*} [Group G] (A V : Subgroup G) : Prop :=
  V ≤ A ∧ IsSolvTwoCompSL23 ↥A (V.subgroupOf A)

@[expose] def SolvableL2PrimeBalance : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (x : X), orderOf x = 2 →
    ∀ V : Subgroup X, IsSolvTwoCompSL23In (centralizer ({x} : Set X)) V →
      oPrimeResidualOf 2 V ≤ pPrimePCore 2 X ∨
        ∃ L : Subgroup X, IsPComponent 2 L ∧ x ∈ normalizer (L : Set X) ∧
          oPrimeResidualOf 2 V ≤ L

end CFSG.GH74.GLS.Balance
