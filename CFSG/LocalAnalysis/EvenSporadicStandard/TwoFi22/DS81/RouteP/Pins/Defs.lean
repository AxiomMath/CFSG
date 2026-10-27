module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Subgroups

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open Subgroup CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

structure Pins (G : Type*) [Group G] (E : Subgroup G)
    (t : G) where
  ψN : ↥(normalizer (E : Set G)) ≃* ↥Model.Zq
  ψH : ↥(centralizer ({t} : Set G)) ≃* ↥Model.Ze
  φH'' : ↥Model.Ze'' →* G
  agree_NH : ∀ (x : Q3) (hN : x ∈ Model.Zq) (hH : x ∈ Model.Ze),
    ((ψN.symm ⟨x, hN⟩ : ↥(normalizer (E : Set G))) : G) =
      ((ψH.symm ⟨x, hH⟩ : ↥(centralizer ({t} : Set G))) : G)
  agree_NH'' : ∀ (x : Q3) (hN : x ∈ Model.Zq) (h'' : x ∈ Model.Ze''),
    ((ψN.symm ⟨x, hN⟩ : ↥(normalizer (E : Set G))) : G) = φH'' ⟨x, h''⟩
  agree_HH'' : ∀ (x : Q3) (hH : x ∈ Model.Ze) (h'' : x ∈ Model.Ze''),
    ((ψH.symm ⟨x, hH⟩ : ↥(centralizer ({t} : Set G))) : G) = φH'' ⟨x, h''⟩

section InfEquiv

variable {X G₀ : Type*} [Group X] [Group G₀]

@[expose] def infEquiv {K M : Subgroup X} {K₀ M₀ : Subgroup G₀} (ψ : ↥K ≃* ↥K₀)
    (hψ : ∀ x : ↥K, (x : X) ∈ M ↔ ((ψ x : ↥K₀) : G₀) ∈ M₀) : ↥(K ⊓ M) ≃* ↥(K₀ ⊓ M₀) where
  toFun b := ⟨ψ ⟨b, b.2.1⟩, (ψ ⟨b, b.2.1⟩).2, (hψ ⟨b, b.2.1⟩).1 b.2.2⟩
  invFun c := ⟨ψ.symm ⟨c, c.2.1⟩, (ψ.symm ⟨c, c.2.1⟩).2,
    (hψ (ψ.symm ⟨c, c.2.1⟩)).2 (by simpa using c.2.2)⟩
  left_inv b := by ext; simp
  right_inv c := by ext; simp
  map_mul' b₁ b₂ := by
    apply Subtype.ext
    have h : (⟨((b₁ * b₂ : ↥(K ⊓ M)) : X), (b₁ * b₂).2.1⟩ : ↥K) =
        ⟨b₁, b₁.2.1⟩ * ⟨b₂, b₂.2.1⟩ := rfl
    show ((ψ ⟨((b₁ * b₂ : ↥(K ⊓ M)) : X), (b₁ * b₂).2.1⟩ : ↥K₀) : G₀) = _
    rw [h, map_mul]
    rfl

end InfEquiv

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
