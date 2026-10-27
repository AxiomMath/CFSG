module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.Data

public noncomputable section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools CFSG.ABGQGroups
open scoped Pointwise

namespace Setting

variable {G : Type} [Group G] (σ : Setting G)

structure IsLayerComplement (J : Subgroup G) : Prop where
  le : J ≤ σ.L₀
  sup_eq : σ.L₀ = J ⊔ σ.ON
  inf_eq : J ⊓ σ.ON = ⊥
  normal : σ.N ≤ Subgroup.normalizer (J : Set G)
  centralizes : J ≤ Subgroup.centralizer (σ.ON : Set G)

structure TIFacts [Finite G] : Prop where
  F₀_abelian : ∀ g ∈ σ.F₀, ∀ h ∈ σ.F₀, g * h = h * g
  F₀_omega : ∀ g ∈ σ.F₀, g ^ 2 = 1 → g ∈ σ.T
  C_eq : oddCoreIn σ.C ⊔ σ.F₀ = σ.C
  commutator_le : ⁅σ.N, σ.N⁆ ≤ σ.L₀
  cyclic : ∀ J : Subgroup G, σ.IsLayerComplement J → IsCyclic (σ.C ⊓ J : Subgroup G)
  centralizer_le : ∀ J : Subgroup G, σ.IsLayerComplement J → ∀ g ∈ σ.C,
    g ∈ Subgroup.centralizer ((σ.C ⊓ J : Subgroup G) : Set G) → g ∈ σ.L
  signalizer_le : ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ U ∈ signalizers σ.N σ.C r, U ≤ σ.L₀
  layer_signalizer : ∀ J : Subgroup G, σ.IsLayerComplement J → ∀ r : ℕ, r.Prime → r ≠ 2 →
    ∀ X ∈ signalizers J σ.C r, X ≠ ⊥ → σ.DeltaEpsMinus ∧ r = σ.p
  layer_signalizer_pair : ∀ J : Subgroup G, σ.IsLayerComplement J → σ.DeltaEpsMinus →
    ∃ Q Qs : Subgroup G, Q ∈ signalizers J σ.C σ.p ∧ Qs ∈ signalizers J σ.C σ.p ∧
      Nat.card Q = σ.q ∧ Nat.card Qs = σ.q ∧ Q ≠ Qs ∧ J = Q ⊔ Qs ∧
      (∃ z ∈ σ.D, TotallyInverted.conjSub z Q = Qs) ∧
      (∀ X ∈ signalizers J σ.C σ.p, X ≤ Q ∨ X ≤ Qs) ∧
      (∀ X : Subgroup G, X ≤ Q → σ.C ≤ Subgroup.normalizer (X : Set G) → X = ⊥ ∨ X = Q) ∧
      (∀ X : Subgroup G, X ≤ Qs → σ.C ≤ Subgroup.normalizer (X : Set G) → X = ⊥ ∨ X = Qs)
  permutable_le : ∀ J : Subgroup G, σ.IsLayerComplement J → ∀ U : Subgroup G, U ≤ σ.N →
    Odd (Nat.card U) → (U : Set G) * (σ.C : Set G) = (σ.C : Set G) * (U : Set G) →
      ∃ (p : ℕ) (X : Subgroup G), p.Prime ∧ X ∈ signalizers J σ.C p ∧ U ≤ σ.C ⊔ X ⊔ σ.ON

theorem TIFacts.C_le_oddCoreIn_sup_D [Finite G] {σ : Setting G} (h : σ.TIFacts) :
    σ.C ≤ oddCoreIn σ.C ⊔ σ.D := by
  calc σ.C = oddCoreIn σ.C ⊔ σ.F₀ := h.C_eq.symm
    _ ≤ oddCoreIn σ.C ⊔ σ.D := sup_le_sup_left inf_le_left _

end Setting

end CFSG.ABGTheoremB
