module

public import CFSG.ClassicalInvolution.Q3.Q3AMTri
public import CFSG.ClassicalInvolution.Q3.Q3AMTriBr
public import CFSG.ClassicalInvolution.Q3.Q3AM289Stmt

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL

section Defs

@[expose] def LayerThinOrS3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Q3T8.Asc77.BadStd8 Ω K J S R T W z t →
      IsIntrinsicU (.sl2 3 1) K z → NoTriangleAtEdge Ω K J → ThinY Ω K z ∨ LayerS3 Ω K z

@[expose] def C28_7_10Y : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Q3T8.Asc77.BadStd8 Ω K J S R T W z t →
      IsIntrinsicU (.sl2 3 1) K z → NoTriangleAtEdge Ω K J → ThinY Ω K z →
        MuIsoE4 Ω W ∨ MuIsoS4 Ω W

@[expose] def CFBY : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Q3T8.Asc77.BadStd8 Ω K J S R T W z t →
      IsIntrinsicU (.sl2 3 1) K z → NoTriangleAtEdge Ω K J → ThinY Ω K z → ¬ MuIsoE4 Ω W

@[expose] def C26_2Y : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Q3T8.Asc77.BadStd8 Ω K J S R T W z t →
      IsIntrinsicU (.sl2 3 1) K z → NoTriangleAtEdge Ω K J → ThinY Ω K z → ¬ MuIsoS4 Ω W

end Defs

section Assembly

theorem thm5Bad3I_of_TNY (hTri : C28_TriB) (hdich : LayerThinOrS3) (h710 : C28_7_10Y)
    (hF : CFBY) (h26 : C26_2Y) (h9 : C28_9S3L) : Thm5Bad3I := by
  intro hIH G _ _ _ Ω K J S R T W z t h hint hb9
  by_cases hT : ∃ K' ∈ omegaNbr Ω K, K' ∈ omegaNbr Ω J
  · obtain ⟨K', hK', hJ'⟩ := hT
    exact hTri hIH G Ω K J S R T W z t K' hb9 ⟨h, hint, hK', hJ'⟩
  · have hN : NoTriangleAtEdge Ω K J := fun K' hK' hJ' => hT ⟨K', hK', hJ'⟩
    rcases hdich G Ω K J S R T W z t h hint hN with hth | hS3
    · rcases h710 G Ω K J S R T W z t h hint hN hth with h4 | h4
      · exact hF G Ω K J S R T W z t h hint hN hth h4
      · exact h26 G Ω K J S R T W z t h hint hN hth h4
    · exact h9 G Ω K J S R T W z t ⟨h, hint, hN, hS3⟩

end Assembly

end CFSG.ClassicalInvolution.Q3.Q3AM
