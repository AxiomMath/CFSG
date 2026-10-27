module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameStmt

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.RouteD
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Balance.BootRank3 (omegaConnected_of_routeD)

section Shape

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

@[expose] def ChainShapeData3 {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData p f X Φ) : Prop :=
  D.card = 2 ∧ ∃ i₀ i₁ : Fin D.card, i₀ ≠ i₁ ∧ D.tag i₀ = .PSL ∧ D.rank i₀ = 2 ∧
    (D.tag i₁ = .PSL ∨ D.tag i₁ = .PSU) ∧ D.rank i₁ = 3

@[expose] def ChainShape3 (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) (z : G) : Prop :=
  ∃ D : LocalLieSystemAt p f (exactFamily Ω z) z, ChainShapeData3 D

theorem ChainShape3.chainShape (h : ChainShape3 p f Ω z) : ChainShape p f Ω z := by
  obtain ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, hr₁⟩ := h
  exact ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, Or.inl hr₁⟩

theorem chainShape3_of_local (hex : ExactMembers Ω)
    (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z)
    (hs : ∃ D : LocalLieSystemAt p f Ω z, ChainShapeData3 D) : ChainShape3 p f Ω z := by
  have h : centralizingMembers (exactFamily Ω z) {z} = centralizingMembers Ω {z} :=
    (centMembers_exactFamily Ω z).trans (exactFamily_eq_centMembers_of_exact hex hcls)
  have key : ∀ S₁ S₂ : Set (Subgroup G), S₁ = S₂ →
      (∃ D : LieSystemData p f (↥(⨆ L ∈ S₁, L) ⧸ classicalInvolutionOddCore ↥(⨆ L ∈ S₁, L))
        (oddQuotientFamily (restrictFamily S₁ (⨆ L ∈ S₁, L))), ChainShapeData3 D) →
      ∃ D : LieSystemData p f (↥(⨆ L ∈ S₂, L) ⧸ classicalInvolutionOddCore ↥(⨆ L ∈ S₂, L))
        (oddQuotientFamily (restrictFamily S₂ (⨆ L ∈ S₂, L))), ChainShapeData3 D := by
    intro S₁ S₂ h
    subst h
    exact id
  exact key _ _ h.symm hs

theorem chainShape3_of_localShapeA (hex : ExactMembers Ω)
    (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z) (h : LocalShapeA p f 2 Ω z) :
    ChainShape3 p f Ω z := by
  obtain ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, hr₁⟩ := h
  exact chainShape3_of_local hex hcls ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, Or.inl ht₁, hr₁⟩

theorem chainShape3_of_localShapeU (hex : ExactMembers Ω)
    (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z) (h : LocalShapeU p f 2 Ω z) :
    ChainShape3 p f Ω z := by
  obtain ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, hr₁⟩ := h
  exact chainShape3_of_local hex hcls ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, Or.inr ht₁, hr₁⟩

end Shape

end CFSG.ClassicalInvolution.Asc77
