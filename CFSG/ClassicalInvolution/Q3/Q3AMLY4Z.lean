module

public import CFSG.ClassicalInvolution.Q3.Q3AMLY4G
public import CFSG.ClassicalInvolution.Q3.Q3AMLY4P04
public import CFSG.ClassicalInvolution.Q3.Q3AMLYShape
public import CFSG.ClassicalInvolution.Q3.Q3AM289Stmt

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

section Layer


theorem c26_2Y_of_9S3L (h9 : C28_9S3L) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
      (K J : Subgroup G) (S : Sylow 2 G) (R T W : Subgroup G) (z t : G),
      BadStd8 Ω K J S R T W z t → IsIntrinsicU (.sl2 3 1) K z → NoTriangleAtEdge Ω K J →
        ThinY Ω K z → ¬ MuIsoS4 Ω W := by
  intro G _ _ _ Ω K J S R T W z t h hint hN _hth hS4
  rcases layer_shape h hint hN with htop | hL3 | hM11 | hS3
  · exact c26_1Y h hint hN htop
  · exact c26_2_of_layerL3M11 h hint (Or.inl hL3) hS4
  · exact c26_2_of_layerL3M11 h hint (Or.inr hM11) hS4
  · exact h9 G Ω K J S R T W z t ⟨h, hint, hN, hS3⟩

end Layer

end CFSG.ClassicalInvolution.Q3.Q3AM
