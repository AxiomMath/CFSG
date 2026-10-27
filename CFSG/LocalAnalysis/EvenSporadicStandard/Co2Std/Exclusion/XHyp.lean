module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.Facts

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion

open Subgroup

variable {V : Type*} [Group V] {X : Type*} [Group X]

structure XHyp (ρ : X →* MulAut V) (Q : Subgroup X) (V₁ V₂ : Subgroup V) (z : X)
    (Q₁ : Subgroup (MulAut ↥V₁)) (t₁ : ↥V₁) : Prop where
  injective : Function.Injective ρ
  elemAb : IsElementaryAbelian 2 V
  inf_eq_bot : V₁ ⊓ V₂ = ⊥
  sup_eq_top : V₁ ⊔ V₂ = ⊤
  mul_self : z * z = 1
  swap : ∀ v : V, v ∈ V₁ ↔ ρ z v ∈ V₂
  centralizer_eq : centralizer ({z} : Set X) = zpowers z ⊔ Q
  res : ∃ e : ↥Q ≃* ↥Q₁, ∀ (q : ↥Q) (v : ↥V₁), (((e q : MulAut ↥V₁) v : ↥V₁) : V) = ρ q v
  module : ModuleFacts Q₁ t₁
  fixed : (∀ x : X, ∀ v : V, ρ z v = v → ρ z (ρ x v) = ρ x v) → zpowers z ⊔ Q = ⊤

@[expose] def XGood (ρ : X →* MulAut V) (Q : Subgroup X) (V₁ V₂ : Subgroup V) (x : X) : Prop :=
  ((∃ q ∈ Q, ∀ v ∈ V₁, ρ x v = ρ q v) ∧ ∃ q ∈ Q, ∀ v ∈ V₂, ρ x v = ρ q v) ∨
    ((∀ v ∈ V₁, ρ x v ∈ V₂) ∧ ∀ v ∈ V₂, ρ x v ∈ V₁)

@[expose] def XConcl (ρ : X →* MulAut V) (Q : Subgroup X) (V₁ V₂ : Subgroup V) (z : X) : Prop :=
  (∃ X₀ : Subgroup X, X₀.Normal ∧ X₀.index = 2 ∧ z ∉ X₀) ∧
    ∃ P : Sylow 2 X, z ∈ P ∧ ∀ x ∈ P, XGood ρ Q V₁ V₂ x

end CFSG.EvenSporadicStandard.Co2Std.Exclusion
