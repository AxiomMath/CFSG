module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6
public import CFSG.Open.GLADefs
import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeTwoTorus
import CFSG.LocalAnalysis.StandardType.GGTableBF4Torus
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLParity
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLTorusBridge
import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeNbrKnownLemmas
import CFSG.LocalAnalysis.StandardType.Marking

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SG

open CFSG.Open CFSG.StandardType
open CFSG.StandardType.SCFourCover (three_dvd_two_pow_add_one_or_sub_one
  largeEvenLabelAll_torusLift_excMinus_threeFive largeEvenLabelAll_torusLift_excPlus_threeFive)

private theorem labelAll_torusLift_four {lab : GLALabel} {r : ℕ} (hr : 4 ≤ r)
    (h : CFSG.StandardType.LargeEvenLabelAll lab fun R _ _ _ =>
      CFSG.StandardType.GGTorusLift 3 r R) :
    CFSG.StandardType.LargeEvenLabelAll lab fun R _ _ _ =>
      CFSG.StandardType.GGTorusLift 3 4 R := fun Q hQ =>
  largeEvenRawDatum_mono (fun _ _ _ _ hq => ⟨hq.1, ggTorusLift_mono Nat.prime_three hq.2 hr⟩)
    (h Q hQ)


theorem labelAll_torusLift_exc {lab : GLALabel} (hlab2 : GLAInLambda2 lab)
    (ht : lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨
      (lab.tag = .F4 ∧ 3 ∣ 2 ^ lab.n - 1)) :
    CFSG.StandardType.LargeEvenLabelAll lab fun R _ _ _ =>
      CFSG.StandardType.GGTorusLift 3 4 R := by
  rcases ht with ht | ht | ht | ht | ⟨ht, h3⟩
  ·
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht
    subst ht
    intro Q hQ
    obtain ⟨K, _, _, hK, hQ⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    exact ⟨K, inferInstance, inferInstance, hK, hQ, TableBExc.E6Three.ggTorusLift_E6_two⟩
  ·
    rcases three_dvd_two_pow_add_one_or_sub_one lab.n with h3 | h3
    · have h := largeEvenLabelAll_torusLift_twE6Add_holds Nat.prime_three hlab2 ⟨ht, h3⟩
      rwa [TwE6Delta.liftRank_three] at h
    · exact largeEvenLabelAll_torusLift_twE6Dvd Nat.prime_three (by norm_num) hlab2 ⟨ht, h3⟩
  ·
    rcases three_dvd_two_pow_add_one_or_sub_one lab.n with h3 | h3
    · exact labelAll_torusLift_four (by norm_num)
        (largeEvenLabelAll_torusLift_excPlus_threeFive (Or.inl ht) h3)
    · exact labelAll_torusLift_four (by norm_num)
        (largeEvenLabelAll_torusLift_excMinus_threeFive (Or.inl ht) h3)
  ·
    rcases three_dvd_two_pow_add_one_or_sub_one lab.n with h3 | h3
    · exact labelAll_torusLift_four (by norm_num)
        (largeEvenLabelAll_torusLift_excPlus_threeFive (Or.inr ht) h3)
    · exact labelAll_torusLift_four (by norm_num)
        (largeEvenLabelAll_torusLift_excMinus_threeFive (Or.inr ht) h3)
  ·
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht h3
    subst ht
    intro Q hQ
    obtain ⟨K, _, _, hK, hQ⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpq : 3 ∣ Nat.card K - 1 := by rw [hK]; exact h3
    exact ⟨K, inferInstance, inferInstance, hK, hQ,
      TableBF4.ggTorusLift_F4 Nat.prime_three (by norm_num) hpq⟩

end CFSG.LocalAnalysis.GLTheoremA.S265.SG

end
