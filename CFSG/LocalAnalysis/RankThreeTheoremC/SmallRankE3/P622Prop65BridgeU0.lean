module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N4P65U0Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

theorem p622Prop65Large_of_stepP65OddE3U0 (h : StepP65OddE3U0) : P622Prop65Large := by
  intro G _ _ hS hD1 _ hU0 p hp3 P M hsit x z hx hz _ F hF1 hFM hcop hodd hBF
  have hprime : p.Prime := sigmaA_prime p hsit.mem_sigmaA
  have hp2 : p ≠ 2 := sigmaA_odd p hsit.mem_sigmaA
  have hp5 : 5 ≤ p := by
    have h2 := hprime.two_le
    have h4 : p ≠ 4 := by
      rintro rfl
      norm_num at hprime
    omega
  exact h G hS hD1 hU0 p hp5 P M hsit x z hx hz F hF1 hFM hcop hodd hBF

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
