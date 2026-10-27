module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieSpor
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLiePSL
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLiePSp
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLiePSU
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieOrth
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieExc
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieTri

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.Assembly.LowTwoRank (StatedLieTag)

theorem outerFixedRankDefAt_twistedB2 : OuterFixedRankDefAt .twistedB2 := by
  intro K _ _ n ℓ f hadm hmodel hT p hp hp5 hℓ α hαp hαin
  obtain ⟨-, -, -, hℓ2, -, -⟩ := hadm
  omega

theorem outerFixedRankDefAt_twistedG2 : OuterFixedRankDefAt .twistedG2 := by
  intro K _ _ n ℓ f hadm hmodel hT p hp hp5 hℓ α hαp hαin
  obtain ⟨-, -, -, hℓ3, -, -⟩ := hadm
  omega

theorem outerFixedRankDefAt_twistedF4 : OuterFixedRankDefAt .twistedF4 := by
  intro K _ _ n ℓ f hadm hmodel hT p hp hp5 hℓ α hαp hαin
  obtain ⟨-, -, -, hℓ2, -, -⟩ := hadm
  omega

theorem outerFixedRankDefAt_Tits : OuterFixedRankDefAt .Tits :=
  fun _ _ _ _ _ _ _ _ hT => absurd rfl hT

section


theorem outerFixedRankDef_holds (t : StatedLieTag) : OuterFixedRankDefAt t := by
  cases t
  · exact outerFixedRankDefAt_PSL
  · exact outerFixedRankDefAt_PSU
  · exact outerFixedRankDefAt_PSp
  · exact outerFixedRankDefAt_POmegaOdd
  · exact outerFixedRankDefAt_POmegaPlus
  · exact outerFixedRankDefAt_POmegaMinus
  · exact outerFixedRankDefAt_G2
  · exact outerFixedRankDefAt_F4
  · exact outerFixedRankDefAt_E6
  · exact outerFixedRankDefAt_E7
  · exact outerFixedRankDefAt_E8
  · exact outerFixedRankDefAt_twistedE6
  · exact outerFixedRankDefAt_trialityD4
  · exact outerFixedRankDefAt_twistedB2
  · exact outerFixedRankDefAt_twistedG2
  · exact outerFixedRankDefAt_twistedF4
  · exact outerFixedRankDefAt_Tits

end

theorem kd291OuterLie_of_cross
    (hC : ∀ t, OuterFixedRankCrossAt t) : KD291OuterLie :=
  kd291OuterLie_of_fixedRank sporadicCarrierOutOdd_holds outerFixedRankDef_holds hC

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
