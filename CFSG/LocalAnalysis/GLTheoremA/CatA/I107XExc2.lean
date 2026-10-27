module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107XHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107EExc

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I107X

open CFSG.Open CFSG.Assembly


@[expose] def TwoRankLowExcRest2 : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (lab : GLALabel), IsSimpleGroup S → Rk2IsLabel S lab → GLAInLambda2 lab →
    ¬ exempt107 lab →
    (lab.tag = .triD4 ∨ lab.tag = .F4 ∨ lab.tag = .twF4 ∨ lab.tag = .twE6) →
    twoRankLow107 lab ≤ CFSG.Open.pRank 2 (⊤ : Subgroup S)

theorem twoRankLowExcRest_of_X2 (h : TwoRankLowExcRest2) :
    CFSG.LocalAnalysis.GLTheoremA.I107E.TwoRankLowExcRest := by
  intro S _ _ lab hS hrk hlab hne htag
  rcases htag with ht | ht | ht | ht | ht | ht | ht
  · exact h S lab hS hrk hlab hne (Or.inl ht)
  · exact h S lab hS hrk hlab hne (Or.inr (Or.inl ht))
  · exact h S lab hS hrk hlab hne (Or.inr (Or.inr (Or.inl ht)))
  · exact CFSG.LocalAnalysis.GLTheoremA.I107E.twoRankLow_E6_holds S lab hS hrk ht
  · exact CFSG.LocalAnalysis.GLTheoremA.I107E.twoRankLow_E7_holds S lab hS hrk ht
  · exact CFSG.LocalAnalysis.GLTheoremA.I107E.twoRankLow_E8_holds S lab hS hrk ht
  · exact h S lab hS hrk hlab hne (Or.inr (Or.inr (Or.inr ht)))

end CFSG.LocalAnalysis.GLTheoremA.I107X

end
