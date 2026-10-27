module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitCAff
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelAut
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ShapeCPrimeData

public section

namespace CFSG.EvenSmallLie.OmegaEight.SplitIn

open Subgroup Matrix CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.SplitC
open CFSG.EvenSmallLie.UnitarySix.YamadaPar
open CFSG.EvenSmallLie.OmegaEight.CPrime (reflRows)

variable {G : Type*} [Group G]

structure OuterLink (ε : Eps) (t : G) (L U Q P : Subgroup G) (a : G) (ψ : V6 → G)
    (p u : Fin 6 → G) (x₀ : G) : Prop where
  link : LinkFacts ε L U Q P a ψ p u
  autCent : AutCent L Q
  mem : x₀ ∈ centralizer ({t} : Set G)
  not_mem : x₀ ∉ L ⊔ zpowers t
  sq_mem : x₀ * x₀ ∈ centralizer (L : Set G)
  act : ∀ v, x₀ * ψ v * x₀⁻¹ = ψ (toMat 6 6 (reflRows ε (n0 ε)) *ᵥ v)
  normalizes_U : ∀ y ∈ U, x₀ * y * x₀⁻¹ ∈ U
  normalizer_Q : ∀ h ∈ centralizer ({t} : Set G), h ∈ normalizer (Q : Set G) →
    h ∈ L ⊔ zpowers t ∨ h * x₀⁻¹ ∈ L ⊔ zpowers t
  embed : ∃ Θ : centralizer ({t} : Set G) →* Equiv.Perm (Fin (Model.aDeg ε)),
    (∀ y, Θ y ∈ Model.AT ε) ∧ (∀ y, Θ y = 1 ↔ (y : G) ∈ zpowers t) ∧
      ∀ v (hv : ψ v ∈ centralizer ({t} : Set G)), Θ ⟨ψ v, hv⟩ = Model.psiTM ε v

structure OuterData (ε : Eps) (L H₀ U Q P : Subgroup G) (ψ : V6 → G) (x₀ : G) : Prop where
  mem : x₀ ∈ H₀
  not_mem : x₀ ∉ L
  sq : x₀ * x₀ = 1
  act : ∀ v, x₀ * ψ v * x₀⁻¹ = ψ (toMat 6 6 (reflRows ε (n0 ε)) *ᵥ v)
  normalizes_U : ∀ y ∈ U, x₀ * y * x₀⁻¹ ∈ U
  normalizer_Q : ∀ h ∈ H₀, h ∈ normalizer (Q : Set G) → h ∈ P ⊔ zpowers x₀

structure Inputs (ε : Eps) (t : G) (L H₀ U Q P : Subgroup G) (a : G) (ψ : V6 → G)
    (p u : Fin 6 → G) (x₀ : G) : Prop where
  setting : Setting ε t L H₀ U Q P (U ⊔ zpowers x₀) a ψ p
  link : LinkFacts ε L U Q P a ψ p u
  autCent : AutCent L Q
  outer : OuterData ε L H₀ U Q P ψ x₀
  card_S₀ : Nat.card (U ⊔ zpowers x₀ : Subgroup G) = 8192
  orth : InducesOrth ε H₀ Q ψ
  levi : ∃ X : Subgroup G, X ≤ centralizer ({t} : Set G) ⊓ normalizer (Q : Set G) ∧
    X ⊓ (Q ⊔ zpowers t) = ⊥ ∧ ∀ σ ∈ orthGroup ε, ∃ g ∈ X, ∀ v, lin ψ g v = σ v
  embed : ∃ J : H₀ →* Equiv.Perm (Fin (Model.aDeg ε)),
    Function.Injective J ∧ ∀ h, J h ∈ Model.AT ε

end CFSG.EvenSmallLie.OmegaEight.SplitIn
