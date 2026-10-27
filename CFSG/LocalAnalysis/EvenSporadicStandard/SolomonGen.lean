module

public import CFSG.Open.FusionDefs
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup

public section

namespace CFSG.EvenSporadicStandard

open Subgroup CFSG.Open

@[expose] def SolomonGen (A : Type) [Group A] : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.SectionRank.IsKGroupCat K → ∀ z : K, orderOf z = 2 →
    fusionZStar K = ⊥ →
    Nonempty (↥(centralizer ({z} : Set K)) ≃* Multiplicative (ZMod 2) × A) →
    ∃ N₁ N₂ : Subgroup K, Nonempty (N₁ ≃* A) ∧ Nonempty (N₂ ≃* A) ∧
      (∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) ∧ Disjoint N₁ N₂ ∧ (N₁ ⊔ N₂).Normal ∧
      (N₁ ⊔ N₂).index = 2 ∧ z ∉ N₁ ⊔ N₂ ∧ N₁.map (MulAut.conj z).toMonoidHom = N₂

end CFSG.EvenSporadicStandard
