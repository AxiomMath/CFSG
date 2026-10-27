module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.T1
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TriD4ThreeSixAux.TwoPoly
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TriD4ThreeSixAux.Six
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterT
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterQ3
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterFieldAny

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Timmesfeld.LangTorus

set_option linter.unusedSectionVars false


theorem center_eq_bot_of_conj_injective_aux {G : Type*} [Group G]
    (h : Function.Injective (MulAut.conj : G →* MulAut G)) : Subgroup.center G = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => h ?_
  rw [map_one]
  ext g
  have := Subgroup.mem_center_iff.1 hz g
  simp only [MulAut.conj_apply, MulAut.one_apply]
  rw [← this]
  group

theorem innerPlaneBalanceAt_trialityD4_three : InnerPlaneBalanceAt .trialityD4 3 :=
  fun q hv p hp hp7 _ hpq he =>
    innerPlaneBalanceAtP_trialityD4_3 d4TwoPoly_holds frobeniusOnRoots_proved t1_pieces
      (fun q hv => center_eq_bot_of_conj_injective_aux (conj_injective_cat_trialityD4 q hv))
      q hv p hp hp7 hp7 hpq he

theorem innerPlaneBalanceAt_trialityD4_six : InnerPlaneBalanceAt .trialityD4 6 :=
  fun q hv p hp hp7 _ hpq he =>
    innerPlaneBalanceAtP_trialityD4_6 (anyKindCommute_of_T anyKindCommuteT_holds)
      anyKindNoFrobenius_of_outer anyKindCommuteThreeFull_holds frobeniusOnRoots_proved t1_pieces
      (fun q hv => center_eq_bot_of_conj_injective_aux (conj_injective_cat_trialityD4 q hv))
      q hv p hp hp7 hp7 hpq he

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
