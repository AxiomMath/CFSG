module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Family
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.L34E9
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.Timmesfeld.Coordinator

open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.LieType.SeitzGeneration
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance

theorem crossCharFamAt_D_two_of_lt_six
    (h : CrossCharFamAt .D fun idx p => p = 3 ∧ ∃ (r : ℕ) (q : TauCeti.PrimePower),
      idx.1 = .D r q ∧ q.card = 2 ∧ r < 6) :
    CrossCharFamAt .D fun idx p => p = 3 ∧ ∃ (r : ℕ) (q : TauCeti.PrimePower),
      idx.1 = .D r q ∧ q.card = 2 := by
  rintro idx hk p hp hp2 hc ⟨h3, r, q, hd, hq⟩
  by_cases hr : 6 ≤ r
  · exact crossCharFamAt_D_two_six idx hk p hp hp2 hc ⟨h3, r, q, hd, hq, hr⟩
  · exact h idx hk p hp hp2 hc ⟨h3, r, q, hd, hq, by omega⟩

theorem crossCharFamAt_twistedD_two_of_lt_six
    (h : CrossCharFamAt .twistedD fun idx p => p = 3 ∧ ∃ (r : ℕ) (q : TauCeti.PrimePower),
      idx.1 = .twistedD r q ∧ q.card = 2 ∧ r < 6) :
    CrossCharFamAt .twistedD fun idx p => p = 3 ∧ ∃ (r : ℕ) (q : TauCeti.PrimePower),
      idx.1 = .twistedD r q ∧ q.card = 2 := by
  rintro idx hk p hp hp2 hc ⟨h3, r, q, hd, hq⟩
  by_cases hr : 6 ≤ r
  · exact crossCharFamAt_twistedD_two_six idx hk p hp hp2 hc ⟨h3, r, q, hd, hq, hr⟩
  · exact h idx hk p hp hp2 hc ⟨h3, r, q, hd, hq, by omega⟩

end CFSG.HardMathSupport.Timmesfeld.Coordinator
