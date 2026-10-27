module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step16Normal
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step16FourProof

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoStandard

theorem step16_of {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    (h4 : Step16NotFourPoints) : Step16 := by
  intro G _ _ A R g E F hF heven
  have hL : TypeL34 (rankTwoQuot A) := hF.typeA₁
  have h2 : Nat.card (pointsIn R (E ⊓ F)) = 2 := by
    rcases card_pointsIn_inf hE16 h11 hF hL with h | h
    · exact h
    · exact absurd h (h4 G A R g E F hF heven)
  exact ⟨le_of_card_pointsIn_inf_eq_two hE16 h11 hF hL heven h2,
    card_pointsIn_eq_six hE16 h11 hF hL h2, exists_normal_perfect hE16 h11 hF hL heven h2,
    exists_outer_of_card_pointsIn_inf_eq_two hE16 h11 hF hL heven h2⟩

theorem step16 {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11) : Step16 :=
  step16_of hE16 h11 (step16NotFourPoints hE16 h11)

end CFSG.ComponentClassification.AS81
