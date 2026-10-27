module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2SporadicSmall
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2SporadicMid
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2SporadicLarge
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2Assembly
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharCert

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

theorem catSL2SporadicBound_of_ON {n : ℕ}
    (hON : ∀ (J : Type) [Group J] [Finite J], IsSimpleGroup J → (∃ a b : J, a * b ≠ b * a) →
      (J ≃* NativeSporadic.ON) → ∀ τ : MulAut J, CatSL2Hyp J τ n → AutTwoBound J n) :
    CatSL2SporadicBound n := by
  intro J _ _ hJ hna hsp τ h
  have hn := two_le_of_catSL2Hyp h
  obtain ⟨s, ⟨e⟩⟩ := hsp
  cases s
  case M11 => exact autTwoBound_M11 hJ hna e hn
  case M12 => exact autTwoBound_M12 hJ hna e hn
  case M22 => exact (catSL2Hyp_false_M22 hJ hna e h).elim
  case M23 => exact (catSL2Hyp_false_M23 hJ hna e h).elim
  case M24 => exact (catSL2Hyp_false_M24 hJ hna e h).elim
  case J1 => exact autTwoBound_J1 hJ hna e hn
  case J2 => exact autTwoBound_J2 hJ hna e hn
  case J3 => exact autTwoBound_J3 hJ hna e hn
  case J4 => exact (catSL2Hyp_false_J4 hJ hna e h).elim
  case HS => exact (catSL2Hyp_false_HS e h).elim
  case McL => exact autTwoBound_McL hJ hna e hn
  case He => exact (catSL2Hyp_false_He hJ hna e h).elim
  case Ru => exact (catSL2Hyp_false_Ru hJ hna e h).elim
  case Suz => exact (catSL2Hyp_false_Suz hJ hna e h).elim
  case ONan => exact hON J hJ hna e τ h
  case Co1 => exact (catSL2Hyp_false_Co1 hJ hna e h).elim
  case Co2 => exact (catSL2Hyp_false_Co2 hJ hna e h).elim
  case Co3 => exact (catSL2Hyp_false_Co3 hJ hna e h).elim
  case Fi22 => exact (catSL2Hyp_false_Fi22 hJ hna e h).elim
  case Fi23 => exact (catSL2Hyp_false_Fi23 hJ hna e h).elim
  case Fi24Prime => exact (catSL2Hyp_false_Fi24 hJ hna e h).elim
  case HN => exact (catSL2Hyp_false_HN hJ hna e h).elim
  case Ly => exact (catSL2Hyp_false_Ly hJ hna e h).elim
  case Th => exact (catSL2Hyp_false_Th hJ hna e h).elim
  case B => exact (catSL2Hyp_false_B hJ hna e h).elim
  case M => exact (catSL2Hyp_false_M hJ hna e h).elim

theorem catSL2SporadicBound_of_three_le {n : ℕ} (hn : 3 ≤ n) : CatSL2SporadicBound n :=
  catSL2SporadicBound_of_ON fun _ _ _ hJ hna e _ _ => autTwoBound_ON hJ hna e hn

theorem catSL2SporadicBound_of_ONOuter (hON : ONOuterSL2Input) (n : ℕ) :
    CatSL2SporadicBound n :=
  catSL2SporadicBound_of_ON fun _ _ _ hJ hna e _ h => catSL2Bound_ON hON hJ hna e h

theorem starPrime_of_gls3 (hGLS : GLS3OddLieAutComponentsInput) {f : ℕ} (hf : 3 ≤ f) :
    StarPrimeStatement f :=
  starPrime_of_inputs hGLS (by omega) (CrossChar.sL2NotOddLieInputAt (by omega))
    (catSL2SporadicBound_of_three_le hf)

theorem starPrime_two_of_inputs (hO : CatSL2OddLieBound 2) (hON : ONOuterSL2Input) :
    StarPrimeStatement 2 :=
  starPrime_of_oddLie_sporadic le_rfl hO (catSL2SporadicBound_of_ONOuter hON 2)

theorem starPrime_of_gls3_of_two_le (hGLS : GLS3OddLieAutComponentsInput)
    (hO : CatSL2OddLieBound 2) (hON : ONOuterSL2Input) {f : ℕ} (hf : 2 ≤ f) :
    StarPrimeStatement f := by
  rcases Nat.lt_or_ge f 3 with h3 | h3
  · obtain rfl : f = 2 := by omega
    exact starPrime_two_of_inputs hO hON
  · exact starPrime_of_gls3 hGLS h3

end CFSG.SeitzReduction.RankOne
