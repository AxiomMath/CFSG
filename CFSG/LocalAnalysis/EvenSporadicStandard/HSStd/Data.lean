module

public import CFSG.LocalAnalysis.EvenSmallLie.CyclicKernel

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup

@[expose] def LayerZeroInvolution (L : Type*) [Group L] (z : L) : Prop :=
  (∀ φ : MulAut L, (∀ x ∈ centralizer ({z} : Set L), φ x = x) → φ * φ = 1) ∧
    ((∃ P : Subgroup L, P ≤ centralizer ({z} : Set L) ∧ ⁅P, P⁆ = P ∧ z ∈ P) ∨
      ∀ φ : MulAut L, (∀ x ∈ centralizer ({z} : Set L), Odd (orderOf x) → φ x = x) →
        φ * φ = 1)

@[expose] def LayerZeroData (L : Type*) [Group L] : Prop :=
  CFSG.EvenSmallLie.FoursGroupCondition L ∧
    (MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)).range.index ∣ 2 ∧
    ∀ z : L, orderOf z = 2 → LayerZeroInvolution L z

end CFSG.EvenSporadicStandard.HSStd
