module

public import CFSG.GH74.Generic.BProg.B3.S3FusionT
public import CFSG.GH74.Generic.BProg.B3.S3Outer

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup

variable {G : Type} [Group G] [Finite G]

theorem prop301T {x y : G} {K A T : Subgroup G} (h : Setup30 G x K A y) (hT : IsZT x y T) :
    (∃ n ∈ normalizer (T : Set G) ⊓ centralizer ({y} : Set G), n * x * n⁻¹ = x * y) ∧
      (∀ g : G, g * x * g⁻¹ ≠ y) ∧
      (∃ S : Subgroup G, IsSylowOf 2 S ⊤ ∧ ∀ s ∈ S, s * y = y * s) ∧
      (∀ S : Subgroup G, IsSylowOf 2 S ⊤ → ¬ ∀ s ∈ S, s * x = x * s) ∧
      x ∈ (_root_.commutator ↥(centralizer ({y} : Set G))).map
        (centralizer ({y} : Set G)).subtype :=
  prop301T_of_outer h hT
    (S3Outer.outerCaseFusion_of h.hyp h.circ h.shape h.src h.rank1 h.y_mem h.y_ord)

end CFSG.GH74.Generic.BProg.B3
