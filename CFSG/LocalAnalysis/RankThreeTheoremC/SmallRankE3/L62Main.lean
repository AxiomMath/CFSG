module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.L62Core
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.L62Situation
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.L62DeltaBack

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

theorem gl83SmallRankLemma62At3_of_kfacts (hT : T29.GL83I291Three)
    (hNC : T29.NoncyclicCentreRank) (hQ : KFactThreeComponentsQRank) (G : Type) [Group G]
    [Finite G] : GL83SmallRankLemma62At3 G := by
  intro hS hU0 P M hs x z hx hz
  have hPM : (P : Subgroup G) ≤ M :=
    (sylow_le_of_isCoreMaxLocal hS hs.mem_sigmaA hs.isCoreMaxLocal).1
  obtain ⟨S, x', z', hD, -, -, -⟩ := l62Data_of_situation hS hU0 hs hx hz
  rcases l62_core hT hNC hQ hD with hc | ⟨hcyc, h9⟩
  · exact Or.inl hc
  · exact Or.inr (smallRankCaseDelta3_of_pCore hPM hcyc h9)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
