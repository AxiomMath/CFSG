module

public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.GLS.TwoThin.G.Pred

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.TwoThin
open scoped commutatorElement

@[expose] def B_p810_J2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Gen4 X →
    (∀ J : Subgroup X, CFSG.IsComponent J → InC2 ↥J ∨ InU2 ↥J) →
    ∀ z : X, orderOf z = 2 → z ∈ center X → CFSG.pCore 2 X = zpowers z →
      CFSG.pPrimeCore 2 X = ⊥ →
      ∀ S : Subgroup X, IsSylowOf 2 S ⊤ → Nat.card ↥S = 2 ^ 7 →
        (∀ s ∈ S, (∀ t ∈ S, s * t = t * s) → s = 1 ∨ s = z) →
        ∀ V : Subgroup X, V ≤ S → z ∈ V → Nat.card ↥V = 32 →
          (∀ x ∈ V, x * x ∈ zpowers z ∧ ∀ y ∈ V, ⁅x, y⁆ ∈ zpowers z) →
          ∀ P : Subgroup X, ⁅P, P⁆ = P → 3 ∣ Nat.card ↥P → False

end CFSG.GH74.GLS
