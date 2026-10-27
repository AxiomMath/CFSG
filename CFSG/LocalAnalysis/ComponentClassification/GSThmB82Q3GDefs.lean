module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHyp

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def L43FixedA6Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Blueprint.LieModel G .PSL 4 3 1 →
    ∀ ℓ : G, orderOf ℓ = 2 → ∀ T : Subgroup G, T ≤ centralizer ({ℓ} : Set G) →
      Group.IsPerfect T → 360 ∣ Nat.card T →
      ∀ α : MulAut G, α * α = 1 → (∀ t ∈ T, α t = t) →
        ((T ⊔ oddCoreIn (fixedSubgroup α)).subgroupOf (fixedSubgroup α)).IsSubnormal →
        α = 1 ∨ α = MulAut.conj ℓ

end CFSG.ComponentClassification.GSThmB
