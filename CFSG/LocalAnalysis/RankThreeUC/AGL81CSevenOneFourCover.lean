module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

@[expose] def SevenOneFourCover : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ L : Subgroup X, CFSG.IsComponent L → L.Normal → CFSG.Open.pRank p L = 1 →
      ∀ S : Subgroup X, IsPGroup p S →
        ∃ W : Subgroup X, Subgroup.centralizer (L : Set X) ≤ W ∧ S ≤ L ⊔ W ∧
          ∃ g ∈ W, ∀ w ∈ W, ∃ n : ℕ, w * (g ^ n)⁻¹ ∈ Subgroup.centralizer (L : Set X)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
