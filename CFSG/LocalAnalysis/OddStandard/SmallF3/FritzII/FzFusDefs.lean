module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY11a

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

section

variable {G : Type} [Group G]

@[expose] def Distinct5 (u a b : G) : Prop :=
  a * b = b * a ∧ u ≠ 1 ∧ a ^ 2 ≠ 1 ∧ b ^ 2 ≠ 1 ∧ a ^ 2 * b ^ 2 ≠ 1 ∧ a ^ 2 ≠ u ∧ b ^ 2 ≠ u ∧
    a ^ 2 * b ^ 2 ≠ u ∧ a ^ 2 ≠ b ^ 2 ∧ a ^ 2 * b ^ 2 ≠ a ^ 2 ∧ a ^ 2 * b ^ 2 ≠ b ^ 2

end

@[expose] def Fz722c : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S T₂ : Subgroup G)
    (x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ : G),
    FzSetting7 t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ →
    ∀ i ∈ fzR6 t x₁ x₂ a₁₂ a₂₂ a₃₂, i ^ 2 = 1 → i ∉ (fourGrp x₁ x₂ : Subgroup G) →
      ¬ IsConj ((x₁ * x₂) ^ 2) i

@[expose] def FzNoPointedEmbedZ3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t x₁ x₂ lam : G) (T₂ : Subgroup G) (a₁₂ a₂₂ a₃₂ : G),
    FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ →
    t ^ 2 = 1 → t * x₁ = x₁ * t → t * x₂ = x₂ * t → x₁ * x₂ = x₂ * x₁ →
    ∀ i ∈ fzR6 t x₁ x₂ a₁₂ a₂₂ a₃₂, i ^ 2 = 1 → i ∉ (fourGrp x₁ x₂ : Subgroup G) →
      ∀ g : G, g * i * g⁻¹ = (x₁ * x₂) ^ 2 →
        ¬ ∀ c ∈ T₂, c * i = i * c → g * c * g⁻¹ ∈ T₂

@[expose] def FzPairAtR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t x₁ x₂ lam : G) (T₂ : Subgroup G) (a₁₂ a₂₂ a₃₂ : G),
    FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ →
    t ^ 2 = 1 → t * x₁ = x₁ * t → t * x₂ = x₂ * t → x₁ * x₂ = x₂ * x₁ →
    ∀ i ∈ fzR6 t x₁ x₂ a₁₂ a₂₂ a₃₂, i ^ 2 = 1 → i ∉ (fourGrp x₁ x₂ : Subgroup G) →
      ∃ a ∈ T₂, ∃ b ∈ T₂, a * i = i * a ∧ b * i = i * b ∧ Distinct5 i a b

@[expose] def FzNoPairAtZ3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t x₁ x₂ lam : G) (T₂ : Subgroup G) (a₁₂ a₂₂ a₃₂ : G),
    FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ →
    t ^ 2 = 1 → t * x₁ = x₁ * t → t * x₂ = x₂ * t → x₁ * x₂ = x₂ * x₁ →
    ∀ a ∈ T₂, ∀ b ∈ T₂, ¬ Distinct5 ((x₁ * x₂) ^ 2) a b

end CFSG.OddStandard.SmallF3.FritzII
