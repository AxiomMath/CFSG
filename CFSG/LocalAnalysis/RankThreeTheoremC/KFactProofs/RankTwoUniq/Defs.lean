module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Reduced
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Catalog

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq

open CFSG.Open Subgroup

@[expose] def K1Core : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (R : Sylow 3 X) (A X₀ B : Subgroup X),
    CFSG.IsKGroup X → CFSG.AGLEmbeddingD2.D2Reduced 3 X R A X₀ →
    IsCyclic (Subgroup.center (R : Subgroup X)) →
    B ≤ R → IsElemAbelian 3 B → Nat.card B = 9 →
    (∀ g : X, B.map (MulAut.conj g).toMonoidHom ≠ A) →
    (∀ z ∈ (R : Subgroup X), orderOf z = 3 → (∀ r ∈ (R : Subgroup X), r * z = z * r) →
      ∀ g : X, g * z * g⁻¹ ∈ B → g * z * g⁻¹ ∈ zpowers z) →
    ∀ W : Subgroup X, B ⊔ A ≤ normalizer (W : Set X) → Nat.Coprime (Nat.card W) 6 → W = ⊥

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq
