module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne.Census3 (IsoLie)

@[expose] def SignalizerTwoGroupKFact : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal → IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) → IsCatalogGroup K → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ B : Subgroup X, IsElemAbelian p B → Nat.card B = p ^ 2 →
      B ⊓ centralizer (K : Set X) = ⊥ →
      ((IsRankTwoSEGroup p K ∧ B ≤ K) ∨
        (p = 3 ∧ IsoLie ↥K (.A 1 ⟨2, 3, by norm_num, by norm_num⟩)) ∨
        (p = 5 ∧ IsoLie ↥K (.suzuki 2))) →
      ∀ T : Subgroup X, IsPGroup 2 T → B ≤ normalizer (T : Set X) →
        ⁅B, T⁆ ≤ centralizer (K : Set X)

end CFSG.LocalAnalysis.RankThreeTheoremC
