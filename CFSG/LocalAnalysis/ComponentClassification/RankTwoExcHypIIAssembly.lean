module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIIRee
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIIG2
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIID4
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIIF4
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIIE7E8
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIIE6
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIIMultProof
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIITwistedE6Two

public section

namespace CFSG.ComponentClassification.RankTwoExcHypII

open Subgroup CFSG.Blueprint CFSG.ComponentClassification.RankTwoStandard

theorem excHypII
    (h2E6 : TwistedE6TwoEvenHypII) : RankTwoExceptional.ExcHypII := by
  intro A _ _ hA hT
  have heven : Even (Nat.card (center A)) → AS76b.HypII A := fun hev => by
    rcases excEvenMultiplier A hA hT hev with h | h | h
    · exact hypII_of_G2 hA le_rfl h
    · exact hypII_of_F4 hA h
    · exact h2E6 A hA h hev
  rcases hT with ⟨m, hm, h⟩ | ⟨t, ht, m, hm, h⟩ | ⟨m, -, h⟩ | h
  · exact hypII_of_G2 hA hm h
  · simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hypII_of_trialityD4 hA h
    · exact hypII_of_F4 hA h
    · rcases Nat.even_or_odd (Nat.card (center A)) with hev | hodd
      · exact heven hev
      · exact hypII_of_E6 hA hm h hodd
    · rcases Nat.even_or_odd (Nat.card (center A)) with hev | hodd
      · exact heven hev
      · exact hypII_of_twistedE6 hA hm h hodd
    · exact hypII_of_E7_E8 hA (Or.inl rfl) hm h
    · exact hypII_of_E7_E8 hA (Or.inr rfl) hm h
  · exact hypII_of_reeTits hA (Or.inl h)
  · exact hypII_of_reeTits (f := 1) hA (Or.inr h)

end CFSG.ComponentClassification.RankTwoExcHypII
