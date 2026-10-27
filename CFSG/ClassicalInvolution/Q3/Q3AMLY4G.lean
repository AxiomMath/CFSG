module

public import CFSG.ClassicalInvolution.Q3.Q3AMLY4E
public import CFSG.ClassicalInvolution.Q3.Q3AMLY4F

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

section Top


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem top_notMem_layerFam (hs : Std8 Ω K J S R T W z t) :
    (⊤ : Subgroup (↥(nbrLayer Ω K z) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω K z))) ∉
      layerFam Ω K z :=
  fun hT => LY4.false_of_thinLayer hs (LY4.thin_of_top_mem_layerFam hs hT)

theorem c26_1Y (h : BadStd8 Ω K J S R T W z t) (_hint : IsIntrinsicU (.sl2 3 1) K z)
    (_hN : NoTriangleAtEdge Ω K J) :
    (⊤ : Subgroup (↥(nbrLayer Ω K z) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω K z))) ∉
      layerFam Ω K z :=
  top_notMem_layerFam h.std

end Top

end CFSG.ClassicalInvolution.Q3.Q3AM
