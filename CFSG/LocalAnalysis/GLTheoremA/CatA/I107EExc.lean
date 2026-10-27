module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107EG2Quot
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107LRest

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I107E

open CFSG.Open CFSG.Assembly

@[expose] def TwoRankLowExcRest : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (lab : GLALabel), IsSimpleGroup S → Rk2IsLabel S lab → GLAInLambda2 lab →
    ¬ exempt107 lab →
    (lab.tag = .triD4 ∨ lab.tag = .F4 ∨ lab.tag = .twF4 ∨ lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨
      lab.tag = .twE6) →
    twoRankLow107 lab ≤ CFSG.Open.pRank 2 (⊤ : Subgroup S)


theorem twoRankLowExc_of_X (h : TwoRankLowExcRest) : CFSG.LocalAnalysis.GLTheoremA.I107L.TwoRankLowExc := by
  intro S _ _ lab hS hrk hlab hne htag
  rcases htag with ht | ht | ht | ht | ht | ht | ht | ht | ht
  · exact twoRankLow_twB2_holds S lab hS hrk ht
  · exact h S lab hS hrk hlab hne (Or.inl ht)
  · exact twoRankLow_G2_holds S lab hS hrk ht
  · exact h S lab hS hrk hlab hne (Or.inr (Or.inl ht))
  · exact h S lab hS hrk hlab hne (Or.inr (Or.inr (Or.inl ht)))
  · exact h S lab hS hrk hlab hne (Or.inr (Or.inr (Or.inr (Or.inl ht))))
  · exact h S lab hS hrk hlab hne (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ht)))))
  · exact h S lab hS hrk hlab hne (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ht))))))
  · exact h S lab hS hrk hlab hne (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ht))))))

end CFSG.LocalAnalysis.GLTheoremA.I107E

end
