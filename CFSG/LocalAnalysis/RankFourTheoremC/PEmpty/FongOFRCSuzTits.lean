module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieDefs
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdRank

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

theorem outerFixedRankCrossAt_Tits : OuterFixedRankCrossAt .Tits :=
  fun _ _ _ _ _ _ _ _ hT => absurd rfl hT

theorem outerFixedRankCrossAt_twistedB2 : OuterFixedRankCrossAt .twistedB2 := by
  intro K _ _ n ℓ f hadm hmodel hT p hp hp5 hℓ hdiv α hαp hαin hrk
  exfalso
  have hS : CFSG.Blueprint.SuzukiModel K ℓ f := by
    rcases hmodel with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, hS⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact hS
  obtain ⟨rfl, -⟩ := hS.1 |> fun h => (⟨h, hS⟩ : ℓ = 2 ∧ _)
  have := CFSG.QuasithinUnique.Id2519.pRank_le_one_suzuki hS hp (by omega)
  omega

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
