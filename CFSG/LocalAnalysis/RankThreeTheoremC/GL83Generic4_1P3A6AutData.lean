module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

@[expose] def A6AutData : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsRankThreeA6 K → ∀ S : Subgroup (MulAut K), IsPGroup 3 S →
    Nat.card S ∣ 3 ^ 2

end CFSG.LocalAnalysis.RankThreeTheoremC
