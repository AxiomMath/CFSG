module

public import CFSG.ClassicalInvolution.Q3.Q3AMLY5Ax03
public import CFSG.ClassicalInvolution.Q3.Q3AMLY5Conj
public import CFSG.ClassicalInvolution.Q3.Q3AMLY5Sect

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL

section Leaf


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
  {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem layer_center_eq_bot_of_layerE4 [IsSimpleGroup G] (h : BadStd8 Ω K J S R T W z t)
    (hint : IsIntrinsicU (.sl2 3 1) K z) (hN : NoTriangleAtEdge Ω K J) (hL : LayerE4 Ω K z) :
    Subgroup.center (↥(nbrLayer Ω K z) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω K z)) = ⊥ := by
  obtain ⟨hsimp, x, y, hxy⟩ := layerE4_simple h hint hN hL
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (↥(nbrLayer Ω K z) ⧸ classicalInvolutionOddCore ↥(nbrLayer Ω K z))) with
    h' | h'
  · exact h'
  · exact absurd (Subgroup.mem_center_iff.mp (h' ▸ Subgroup.mem_top x) y).symm hxy

theorem e1Y_of_sect (hsec : SectionLeafY) : E4AxisLeafY := by
  intro G _ _ _ Ω K J S R T W z t hset
  exact e1Y_of_center_eq_bot hset
    (layer_center_eq_bot_of_layerE4 hset.bad hset.hint hset.noTri
      (hsec G Ω K J S R T W z t hset))

theorem e1Y_proved : E4AxisLeafY := e1Y_of_sect e2Y_proved

end Leaf

end CFSG.ClassicalInvolution.Q3.Q3AM
