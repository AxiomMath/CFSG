module

public import CFSG.HardMathSupport.Timmesfeld.Torality.LangAssembly

public section

namespace CFSG.HardMathSupport.Timmesfeld.Torality

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.CrossChar

section


theorem langToralPlane_F4_three_of_bar (hbar : PlanesToralBar Tag.F4 3) :
    LangToralPlane Tag.F4 3 :=
  langToralPlane_of_bar Nat.prime_three hbar

theorem langToralPlane_E7_three_of_bar (hbar : PlanesToralBar Tag.E7 3) :
    LangToralPlane Tag.E7 3 :=
  langToralPlane_of_bar Nat.prime_three hbar

theorem langToralPlane_E8_three_of_bar (hbar : PlanesToralBar Tag.E8 3) :
    LangToralPlane Tag.E8 3 :=
  langToralPlane_of_bar Nat.prime_three hbar

theorem f4ThreeInnerNonsplitLarge_of_bar (hbar : PlanesToralBar Tag.F4 3)
    (hT1 : ∀ w : WeylGroup Tag.F4, LangTorusPlaneBalance Tag.F4 w 3 ThreeLargeQ) :
    F4ThreeInnerNonsplitLarge :=
  f4ThreeInnerNonsplitLarge_of_toral (langToralPlane_F4_three_of_bar hbar) hT1

theorem e7ThreeInnerNonsplitLarge_of_bar (hbar : PlanesToralBar Tag.E7 3)
    (hT1 : ∀ w : WeylGroup Tag.E7, LangTorusPlaneBalance Tag.E7 w 3 fun q => ¬ 3 ∣ q ∧ q ≠ 2) :
    E7ThreeInnerNonsplitLarge :=
  e7ThreeInnerNonsplitLarge_of_toral (langToralPlane_E7_three_of_bar hbar) hT1

theorem e8ThreeInnerNonsplitLarge_of_bar (hbar : PlanesToralBar Tag.E8 3)
    (hT1 : ∀ w : WeylGroup Tag.E8, LangTorusPlaneBalance Tag.E8 w 3 ThreeLargeQ) :
    E8ThreeInnerNonsplitLarge :=
  e8ThreeInnerNonsplitLarge_of_toral (langToralPlane_E8_three_of_bar hbar) hT1

theorem e8FiveToralPlane_of_bar (hbar : PlanesToralBar Tag.E8 5) : E8FiveToralPlane :=
  langToralPlane_E8_five_iff.1 (langToralPlane_of_bar (by norm_num) hbar)

end

end CFSG.HardMathSupport.Timmesfeld.Torality
