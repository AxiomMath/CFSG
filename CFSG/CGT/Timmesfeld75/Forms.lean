module

public import CFSG.CGT.Timmesfeld75.Targets
public import CFSG.CGT.Timmesfeld75.NodeDerivation

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

@[expose] def TimmesfeldTransitivityTI : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), IsElemAbelian 2 L →
    (∀ g : X, L ⊓ conjSubgroup g⁻¹ L = ⊥ ∨ L ⊓ conjSubgroup g⁻¹ L = L) →
    (∀ g : X, conjSubgroup g⁻¹ L ≤ Subgroup.normalizer (L : Set X) → conjSubgroup g⁻¹ L = L) →
    (∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥) →
    ∀ x ∈ L, x ≠ 1 → ∀ y ∈ L, y ≠ 1 → ∃ g ∈ Subgroup.normalizer (L : Set X), g * x * g⁻¹ = y

theorem transitivityTI_of_transitivity (h : TimmesfeldTransitivity) : TimmesfeldTransitivityTI :=
  fun X _ _ L hel hTI hWC hO x hx hx1 y hy hy1 =>
    h X L (isWC_of_corBHyp (corBHyp_of_ti_of_weaklyClosed hel hTI hWC)) hO x hx hx1 y hy hy1

end CFSG.CGT.Timmesfeld75
