module

public import CFSG.GH74.Generic.BProg.B3.S3FusionTF
public import CFSG.GH74.Generic.BProg.B3.S3Pump305
public import CFSG.GH74.Generic.BProg.B3.S3Pump9

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup

variable {G : Type} [Group G] [Finite G]

theorem prop304 {x y : G} {K A : Subgroup G} (h : Setup30 G x K A y) :
    pLayerOf 2 (centralizer ({x} : Set G)) = K ∧
      pLayerOf 2 (centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G)) = Ly K y := by
  obtain ⟨T, hT, -⟩ := Setup30.exists_T h
  exact S3Pump304.prop304_of_F h hT (prop301T h hT)

theorem thm9_l3_rank1 {x y : G} {K A : Subgroup G} (h : Setup30 G x K A y) :
    IsPCompIn 2 (centralizer ({y} : Set G)) (pumpUp 2 (Ly K y) y) ∧
      x ∈ normalizer ((pumpUp 2 (Ly K y) y : Subgroup G) : Set G) := by
  obtain ⟨T, hT, -⟩ := Setup30.exists_T h
  exact S3Pump9.thm9_l3_rank1_of_F h hT (prop301T h hT)

theorem prop305 {x y : G} {K A : Subgroup G} (h : Setup30 G x K A y) :
    pLayerOf 2 (CxK y (pumpUp 2 (Ly K y) y) ⊓ centralizer ({x} : Set G)) = ⊥ ∧
      ∀ u ∈ CxK y (pumpUp 2 (Ly K y) y) ⊓ centralizer ({x} : Set G), u * u = 1 →
        u = 1 ∨ u = x ∨ u = y ∨ u = x * y := by
  obtain ⟨T, hT, -⟩ := Setup30.exists_T h
  exact S3Pump305.prop305_of_F h hT (prop301T h hT)

end CFSG.GH74.Generic.BProg.B3
