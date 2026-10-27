module

public import CFSG.ClassicalInvolution.Q3.Q3AM289Pair
public import CFSG.ClassicalInvolution.Q3.Q3AM289VtxZ
public import CFSG.ClassicalInvolution.Q3.Q3AM289Vtx
public import CFSG.ClassicalInvolution.Q3.Q3AM289Link

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL

section Main


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem s3_axis_of_setting (h : S3Setting Ω K J S R T W z t) : ∃ s : G, S3AxisL Ω K J z t s :=
  exists_s3Axis_of_pair h.bad h.noTri (not_mem_nbrLayer_of_layerS3 h.bad h.layer)
    (layerS3Pair_of_layerS3 h.bad h.layer)

theorem c28_9s3L_of_vertexA (hA : S3VertexALeaf) :
    C28_9S3L := by
  intro G _ _ _ Ω K J S R T W z t h
  obtain ⟨s, hs⟩ := s3_axis_of_setting h
  obtain ⟨J₂, hJ₂, hu₂⟩ := s3Nbr2 h hs
  obtain ⟨J₁, hJ₁, hu₁, -, -⟩ := hs.nbr
  exact s3_false_of_frame h.bad hs
    (hyp51At_z_of_three_members h.bad hJ₁ hu₁ hJ₂ hu₂ hs.comm_z hs.comm_t hs.indep)
    (s3_vertexT h hs hJ₂ hu₂) (hA G Ω K J S R T W z t h s hs ⟨J₂, hJ₂, hu₂⟩)
    (s3_link h hs)

end Main

end CFSG.ClassicalInvolution.Q3.Q3AM
