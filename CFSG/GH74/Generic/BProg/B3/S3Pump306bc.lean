module

public import CFSG.GH74.Generic.BProg.B3.S3Pump306bcMain
public import CFSG.GH74.Generic.BProg.B3.S3FusionTF

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup

variable {G : Type} [Group G] [Finite G]

theorem prop306bc {x y : G} {K A : Subgroup G} (h : Setup30 G x K A y) {H₁ : Subgroup G}
    (hH₁ : IsPCompIn 2 (centralizer ({y} : Set G)) H₁) (hne : H₁ ≠ pumpUp 2 (Ly K y) y) :
    x ∈ normalizer (H₁ : Set G) ∧ y ∈ H₁ ∧ x ∉ centralizerSection H₁ (pPrimeCoreOf 2 H₁) ∧
      ((∃ H₂ : Subgroup G, IsPCompIn 2 (centralizer ({y} : Set G)) H₂ ∧ H₂ ≠ H₁ ∧
          H₂ ≠ pumpUp 2 (Ly K y) y) →
        ∀ u ∈ H₁ ⊓ centralizer ({x} : Set G), orderOf u = 2 → u = y) := by
  obtain ⟨T, hT, -⟩ := Setup30.exists_T h
  exact S3Pump306.prop306bc_of_F h hT (prop301T h hT) hH₁ hne

end CFSG.GH74.Generic.BProg.B3
