module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.ABGLocalTools Subgroup

@[expose] def KFactL34SylowCentralizer : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsRankThreeL34 K → ∀ (S : Sylow 3 K) (u : K),
    u ∈ (S : Subgroup K) → u ≠ 1 → centralizer ({u} : Set K) = (S : Subgroup K)

end CFSG.LocalAnalysis.RankThreeTheoremC
