module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatTwoLayerC5PSL
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatTwoLayerC5PSU
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatTwoLayerC5PSp
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatTwoLayerC5Omega
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatTwoLayerC5Exc1
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatTwoLayerC5Exc2

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat

open CFSG

theorem fiveTwoLayer_char5_vacuous (τ : Open.StatedLieTag)
    (hτ : τ = .twistedB2 ∨ τ = .twistedG2 ∨ τ = .twistedF4 ∨ τ = .Tits) :
    FiveTwoLayerCharFiveClause τ := by
  intro S _ _ _ _ ⟨n, f, hm⟩
  exfalso
  have hadm := hm.admissible
  rcases hτ with rfl | rfl | rfl | rfl <;> simp [Open.StatedLieAdmissible] at hadm

theorem fiveTwoLayer_char5
    (τ : Open.StatedLieTag) : FiveTwoLayerCharFiveClause τ := by
  cases τ
  exacts [TwoL5.fiveTwoLayer_char5_PSL, TwoL5.fiveTwoLayer_char5_PSU,
    TwoL5.fiveTwoLayer_char5_PSp, TwoL5.fiveTwoLayer_char5_POmegaOdd,
    TwoL5.fiveTwoLayer_char5_POmegaPlus, TwoL5.fiveTwoLayer_char5_POmegaMinus,
    TwoL5.fiveTwoLayer_char5_G2, TwoL5.fiveTwoLayer_char5_F4, TwoL5.fiveTwoLayer_char5_E6,
    TwoL5.fiveTwoLayer_char5_E7, TwoL5.fiveTwoLayer_char5_E8,
    TwoL5.fiveTwoLayer_char5_twistedE6, TwoL5.fiveTwoLayer_char5_trialityD4,
    fiveTwoLayer_char5_vacuous _ (by decide), fiveTwoLayer_char5_vacuous _ (by decide),
    fiveTwoLayer_char5_vacuous _ (by decide), fiveTwoLayer_char5_vacuous _ (by decide)]

end CFSG.ComponentClassification.SolMax.FiveCat
