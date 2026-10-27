module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.L28.ThreeQuotient.Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.LieAll

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.L28

open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree

section Lie


theorem lieThreeDich_holds : LieThreeDich := by
  intro K _ _ hs hnab _ hmodel
  obtain ⟨t, n, ℓ, f, hadm, hmodel⟩ := hmodel
  by_cases h3 : 3 ∣ Nat.card K
  · rcases (dichThreeLieAt_of_tags dichLieDef_all dichLieCross_all K hs hnab t n ℓ f hadm hmodel
      h3).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by rw [Nat.factorization_eq_zero_of_not_dvd h3]; omega)))

end Lie

section Heavy


theorem kFactL28ThreeQuotient_holds : KFactL28ThreeQuotient :=
  kFactL28ThreeQuotient_of_lieThreeDich lieThreeDich_holds

end Heavy

end CFSG.LocalAnalysis.RankThreeTheoremC.L28
