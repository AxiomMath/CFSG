module

public import CFSG.GH74.GLS.C3.Layer1.Th2P412QT
public import CFSG.GH74.GLS.C3.Layer1.Th2P85AltSE
public import CFSG.GroupTheory.InvolutionPow
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.GH74.GLS.Th2.AltCv

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin
  CFSG.GH74.GLS.Th2.P85 CFSG.GH74.GLS.Th2.P85.Alt CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer1.Bk CFSG.GH74.GLS.Th2.P412

@[expose] def TIMOutQ {G : Type} [Group G] (M S : Subgroup G) (x v : G) (hxM : x ∈ M)
    (hvM : v ∈ M) : Prop :=
  ∃ E : Subgroup ↥M, E ≤ S.subgroupOf M ∧ (⟨x, hxM⟩ : ↥M) ∈ E ∧ (⟨v, hvM⟩ : ↥M) ∈ E ∧
    Nat.card E = 8 ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a * a = 1) ∧
    (∀ s ∈ S.subgroupOf M, ∀ y ∈ E, s * y * s⁻¹ ∈ E) ∧
    (∀ y ∈ S.subgroupOf M, (y * y = 1 ∧ y ≠ 1 ∧ y * (⟨v, hvM⟩ : ↥M) = ⟨v, hvM⟩ * y ∧
        IsConj (⟨x, hxM⟩ : ↥M) y ∧ IsConj (⟨x, hxM⟩ : ↥M) (y * ⟨v, hvM⟩)) ↔
      (y ∈ E ∧ y ≠ 1 ∧ y ≠ ⟨v, hvM⟩)) ∧
    (∀ y ∈ E, y ≠ 1 → y ≠ ⟨v, hvM⟩ → ∃ c : ↥M, c * ⟨v, hvM⟩ = ⟨v, hvM⟩ * c ∧
        c * ⟨x, hxM⟩ * c⁻¹ = y) ∧
    (∃ s ∈ S.subgroupOf M, s * s = 1 ∧ s ∉ E) ∧
    (∀ s ∈ S.subgroupOf M, (∀ t ∈ S.subgroupOf M, s * t = t * s) → s * s = 1 → s ≠ 1 →
      s = ⟨v, hvM⟩)

variable {G : Type} [Group G] [Finite G]

end CFSG.GH74.GLS.Th2.AltCv

