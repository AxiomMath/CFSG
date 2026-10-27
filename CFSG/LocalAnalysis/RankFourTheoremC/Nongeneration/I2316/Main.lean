module

public import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.I2316.Families
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneKFacts
public import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.KFacts

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.I2316

open CFSG.AGLEmbedding CFSG.Open

theorem gl83I2316_of_families (h241 : GL83I241) (hOut : KFactSmallOutPPrime)
    (hU : ∀ (p : ℕ) (d : TauCeti.ValidLieTypeIndex), p.Prime → p ≠ 2 → IsUnitaryIndex p d → 2 ≤
        d.1.fieldExponent → PlanesGenerate p (CatGroup
        d)) (hR : ∀ (p : ℕ) (d : TauCeti.ValidLieTypeIndex), IsReeGTwoIndex p d
        → PlanesGenerate p (CatGroup d)) : GL83I2316 := by
  intro K _ _ hs hnab hc p hp hp2 T hT hΓ E hE hEc hnot
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hAut : Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2
  · by_cases hL34 : p = 3 ∧ IsLinThreeFour K
    · obtain ⟨hp3, hK⟩ := hL34
      subst hp3
      exact planesGenerate_of_isLinThreeFour hK E hE hEc hnot
    · exfalso
      apply hnot
      intro e he
      exact hOut K hs hnab hc p hp hp2 T hT hΓ hAut hL34 e
        ⟨1, by rw [pow_one]; exact hE.2 e he⟩
  · obtain ⟨d, hd, ⟨ε⟩⟩ := h241.2 K hs hnab hc p hp hp2 T hT hΓ hAut
    rcases hd with ⟨n, -, hd⟩ | ⟨hd, hexp⟩ | hd
    · exact planesGenerate_of_mulEquiv ε.symm (planesGenerate_of_isLinTwoIndex hp2 hd) E hE hEc hnot
    · exact planesGenerate_of_mulEquiv ε.symm (hU p d hp hp2 hd hexp) E hE hEc hnot
    · exact planesGenerate_of_mulEquiv ε.symm (hR p d hd) E hE hEc hnot

end CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.I2316
