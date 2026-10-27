module

public import CFSG.GH74.QTGen4.Recog.Ku.Defs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.HSType

variable {G : Type} [Group G]

@[expose] def KuClose' (T M H P : Subgroup G) (z : G)
    (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z) : Prop :=
  ∃ y₂ t j t₁ : G, y₂ ∈ oTwoUpper M ⊓ Ψ.L2 ∧ orderOf y₂ = 3 ∧
    t ∈ M ⊓ Subgroup.normalizer (kuV2 T M : Set G) ∧ t ∉ oTwoUpper M ∧ t * t = 1 ∧
    t * y₂ * t⁻¹ = y₂⁻¹ ∧
    j ∈ Ψ.L2 ∧ j ∉ oTwoUpper M ∧ j * j = 1 ∧ j * y₂ * j⁻¹ = y₂⁻¹ ∧
    (t * j) ^ 3 = 1 ∧
    t₁ ∈ oTwoUpper M ∧ t₁ ∉ kuN P H ∧ t₁ * t₁ = 1 ∧ t₁ * y₂ * t₁⁻¹ = y₂⁻¹ ∧
    orderOf (t₁ * j) ≤ 3

end CFSG.GH74.QTGen4.Ku
