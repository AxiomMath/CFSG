module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111Config
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111DataBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
open Hyp111

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem Hyp111.Hyp111B3.mono {p : ℕ} {H Q Q' : Subgroup G}
    {J : Subgroup (H ⧸ primeComplementCore (G := H) p)} (h : Hyp111B3 p H Q J) (hQ : Q ≤ Q') :
    Hyp111B3 p H Q' J :=
  fun S hS hSH hQS => h S hS hSH (hQ.trans hQS)

end CFSG.LocalAnalysis.RankThreeTheoremC
