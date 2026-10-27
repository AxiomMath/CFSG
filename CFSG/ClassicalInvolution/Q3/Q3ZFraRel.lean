module

public import CFSG.ClassicalInvolution.Q3.Q3ZFraFrame
public import CFSG.ClassicalInvolution.Q3.Q3WALoc
public import CFSG.ClassicalInvolution.Q3.Q3WShape

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Z

open CFSG.Assembly.LowTwoRank

section Rel


@[expose] def C3A2Rel : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), Q3W.RouteD3Setup K z →
      Q3W.LocalShapeC3 1 (CompData.model .PSp 2) (conjClass3 K) z →
      Q3W.LocalOddThreeFree3 (conjClass3 K) z → ∀ fr : C3Frame G (conjClass3 K),
        ∃ T₀ ∈ shortNodes fr.Θ₀₁, ∃ T₁ ∈ shortNodes fr.Θ₁₂,
          ∃ W, WeakCT.LinearBlockStandardPair (GaloisField 3 1) W T₀ T₁

theorem chain_of_c3A2Rel (h : C3A2Rel) {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) {K : Subgroup G} {z : G} (hR : Q3W.RouteD3Setup K z)
    (hshape : Q3W.LocalShapeC3 1 (CompData.model .PSp 2) (conjClass3 K) z)
    (hO3 : Q3W.LocalOddThreeFree3 (conjClass3 K) z) (fr : C3Frame G (conjClass3 K)) :
    ∃ U : Fin 3 → Subgroup G, U 2 ∈ conjClass3 K ∧ (∀ a ∈ U 0, ∀ b ∈ U 2, a * b = b * a) ∧
      (∃ W, WeakCT.LinearBlockStandardPair (GaloisField 3 1) W (U 0) (U 1)) ∧
      (∃ W, Models.SymplecticPairs.SymplecticBlockStandardPair (GaloisField 3 1) W (U 2)
        (U 1)) := by
  obtain ⟨T₀, h₀, T₁, h₁, hA⟩ := h G hnab K z hR hshape hO3 fr
  exact chain_of_frame fr h₀ h₁ hA

end Rel

end CFSG.ClassicalInvolution.Q3.Q3Z
