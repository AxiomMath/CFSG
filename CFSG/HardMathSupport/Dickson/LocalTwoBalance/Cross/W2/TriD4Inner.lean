module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.FamOpen
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TriD4InnerAux.Main
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.T1
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterT
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterThree
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterFieldAny
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TriD4InnerAux.Two
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Timmesfeld.LangTorus

set_option linter.unusedSectionVars false

section Main


theorem triD4InnerThreeBalance_holds : TriD4InnerThreeBalance := by
  intro q hv hq3
  by_cases hq : q.p ^ q.exponent = 2
  · obtain ⟨hp2, he1⟩ := (Nat.prime_two.pow_eq_iff).1 hq
    exact innerPlaneBalance_cat_triD4_two hp2 he1 hv
  · obtain ⟨K, _, _, σ, hK, hσ, -, ⟨e⟩⟩ := exists_catEquiv_trialityD4 q hv
    refine InnerPlaneBalance.of_mulEquiv e ?_
    obtain ⟨hAK, hAF, hbig⟩ : AnyKindCommute ∧ AnyKindNoFrobenius ∧ ThreeBigComponents :=
      ⟨anyKindCommute_of_T anyKindCommuteT_holds, anyKindNoFrobenius_of_outer,
        threeBigComponents_holds⟩
    exact innerPlaneBalance_graphFixedRootGroup_D4_three t1_pieces hAK hAF hbig q.prime_p hq3
      q.exponent_pos hq K hK σ hσ

end Main

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
