module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

@[expose] def U43OuterOdd : Prop :=
  ∀ (U : Type) [Group U] [Finite U], IsQuasisimple U → IsTwoU43 U →
    ∀ α : MulAut U, Odd (orderOf α) → ∃ u : U, α = MulAut.conj u

@[expose] def U43CentTwoPlus : Prop :=
  ∀ (U : Type) [Group U] [Finite U], IsQuasisimple U → IsTwoU43 U →
    ∀ Q₁ Q₂ : Subgroup U,
      Nonempty (↥Q₁ ≃* QuaternionGroup 2) → Nonempty (↥Q₂ ≃* QuaternionGroup 2) →
      ⁅Q₁, Q₂⁆ = ⊥ → Nat.card ↥(Q₁ ⊔ Q₂) = 32 → (Q₁ ⊔ Q₂) ⊓ Subgroup.center U = ⊥ →
      IsPGroup 2 (Subgroup.centralizer (((Q₁ ⊔ Q₂ : Subgroup U) : Subgroup U) : Set U))

end CFSG.OddStandard.SmallF3.Omega
