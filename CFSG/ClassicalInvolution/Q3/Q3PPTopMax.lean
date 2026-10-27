module

public import CFSG.ClassicalInvolution.Q3.Q3PPTop
public import CFSG.ClassicalInvolution.Q3.Q3KCMaxAlpha

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3PP

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.Assembly.Dichotomy CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3OF
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3NM

section TopMax


@[expose] def EdgeTwinInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    RouteD3Setup K z → (∃ a b : G, a * b ≠ b * a) →
      ∀ (K₁ K₂ : Subgroup G) (z₁ z₂ : G), EdgeData K K₁ K₂ z₁ z₂ →
        EdgeThirdFree K K₁ K₂ z₁ z₂ → NonClassicalAt (conjClass3 K) (z₁ * z₂) →
        ¬ (TwinFreeAt (conjClass3 K) K₁ z₁ ∧ TwinFreeAt (conjClass3 K) K₂ z₂) →
          alphaCore (Subgroup.closure ({z₁, z₂} : Set G)) = ⊥


theorem alphaCent3EdgesAtSetup_of_twin (hOA : OddAutLayerRigidHyp) (hTwin : EdgeTwinInput) :
    AlphaCent3EdgesAtSetup := by
  intro G _ _ _ K z hR hnab K₁ K₂ z₁ z₂ h
  have he : IsEdge3 (conjClass3 K) K₁ K₂ z₁ z₂ :=
    ⟨h.mem₁, h.mem₂, h.cls₁, h.cls₂, h.comm, h.ne⟩
  rcases edge_triple_or_noTripleThrough (conjClass3 K) K₁ K₂ z₁ z₂ with
    ⟨M, hM, m, hm, hc₁, hc₂, hind⟩ | hno
  · exact alphaCore_edge_eq_bot_of_triple_max hR he hM hm hc₁ hc₂ hind
  · exact h.alphaCore_edge_eq_bot_of_noTriple hOA hR hnab hno
      (hTwin G K z hR hnab K₁ K₂ z₁ z₂ h hno) mfComp_g2 mfComp_trialityD4

theorem commutingProductP1Input3_of_twin (hOA : OddAutLayerRigidHyp) (hTwin : EdgeTwinInput) :
    Q3TY.CommutingProductP1Input3 :=
  commutingProductP1Input3_of_edgesAtSetup (alphaCent3EdgesAtSetup_of_twin hOA hTwin) hOA

end TopMax

end CFSG.ClassicalInvolution.Q3.Q3PP
