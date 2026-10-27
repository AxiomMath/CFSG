module

public import CFSG.LargeExtraspecial.S14Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.LargeExtraspecial.S4

@[expose] def NQPlus6Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G) (t : S.O),
    Stage S g t → Config.omegaPlus6.Occurs S g t → IsExtraspecialPGroup 2 (Nbar S g t) →
      ∃ U₁ U₂ : Subgroup S.O, zpowers t ≤ U₁ ∧ U₁ ≤ Nbar S g t ∧ zpowers t ≤ U₂ ∧
        U₂ ≤ Nbar S g t ∧ (∀ r ∈ Rbar S g t, ∀ u ∈ U₁, r * u * r⁻¹ ∈ U₁) ∧
        (∀ r ∈ Rbar S g t, ∀ u ∈ U₂, r * u * r⁻¹ ∈ U₂) ∧ U₁ ⊓ U₂ = zpowers t ∧
        Nat.card U₁ = 2 ^ 5 ∧ Nat.card U₂ = 2 ^ 5 ∧
        ∀ D : Subgroup S.O, zpowers t ≤ D → D ≤ Nbar S g t →
          (∀ r ∈ Rbar S g t, ∀ d ∈ D, r * d * r⁻¹ ∈ D) →
            D = zpowers t ∨ D = U₁ ∨ D = U₂ ∨ D = Nbar S g t

end CFSG.LargeExtraspecial.S14
