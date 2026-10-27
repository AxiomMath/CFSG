module

public import CFSG.ClassicalInvolution.Q3.Q3AMLY5A01
public import CFSG.ClassicalInvolution.Q3.Q3T8B14E

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Uniform
open scoped MatrixGroups commutatorElement

local notation "𝔽₃" => GaloisField 3 1

section Vertex


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem hyp51At_vertexAY [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hN : Q3AM.NoTriangleAtEdge Ω K J) {w : G}
    (hw2 : w * w = 1) (hwz : z * w = w * z) (hwt : t * w = w * t) (hne : w ≠ t)
    {R₀ : Subgroup G} (hR₀ : IsSylow2In R₀ K) (hwR : ∀ r ∈ R₀, r * w = w * r)
    (hnJ : conjSub w J = J) {J₁ : Subgroup G} (hJ₁K : J₁ ∈ omegaNbr Ω K)
    (hJ₁w : IsUniqueInvolution J₁ w)
    (hshape : LayerShapeAt Ω K J (z * t)) {B : Subgroup G}
    (hB : CFSG.Open.IsElemAbelian 2 B) (hBgen : B = Subgroup.closure ({z, w, z * t} : Set G)) :
    Hyp51At B (z * t) :=
  hyp51At_vertexA_of_class hs hwz hwt (fun hdisc hwN =>
    T8W.layer_class_psl4Y hs hN hw2 hwz hwt hne hR₀ hwR hnJ hJ₁K hJ₁w hdisc hwN) hshape hB hBgen

end Vertex

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
