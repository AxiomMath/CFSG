module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

@[expose] def KFactL34ThreeExponent : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal →
    centralizer (K : Set X) = ⊥ → IsRankThreeL34 ↥K →
    ∀ g : X, (∃ n : ℕ, g ^ 3 ^ n = 1) → g ^ 3 = 1

end CFSG.LocalAnalysis.RankThreeTheoremC
