module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.ABGLocalTools Subgroup

@[expose] def KFactL34OuterCentralizer : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal →
    centralizer (K : Set X) = ⊥ → IsRankThreeL34 ↥K →
    ∀ T : Subgroup X, T ≤ K → IsSylowOf 3 T K → ∀ y ∈ normalizer (T : Set X), y ∉ K →
      y ^ 3 = 1 → ¬ (centralizer ({y} : Set X) ⊓ K ≤ normalizer (T : Set X))

end CFSG.LocalAnalysis.RankThreeTheoremC
