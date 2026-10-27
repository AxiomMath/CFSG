module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.BMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.BD2Count
public import CFSG.Monster.B.CTIB.FourClasses
public import CFSG.Monster.B.CTIB.UniqueComponent

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HypOne.BabyHyp

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS CFSG.Monster.Existence
  CFSG.Monster.B.GSide CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.CTIB
  CFSG.ComponentClassification.M12Cover


theorem babyInv_two_t2DS :
    BabyInv 2 ((sEquiv.symm.trans iotaEquiv.symm : Shat ≃* NativeSporadic.B) t2DS) := by
  refine ⟨?_, ?_⟩
  · have h := @MulEquiv.orderOf_eq Shat _ NativeSporadic.B Units.instMonoid
      (sEquiv.symm.trans iotaEquiv.symm) t2DS
    rw [h]
    exact orderOf_t2DS
  · have h := @ComponentClassification.M12Cover.centralizerEquiv Shat NativeSporadic.B _
      Units.instGroup (sEquiv.symm.trans iotaEquiv.symm) t2DS
    rw [← Nat.card_congr h.toEquiv, natCard_centralizer_t2DS]
    rfl

theorem babyRootClassLarge_two : BabyRootClassLarge 2 := by
  intro a ha
  have hconj : IsConj ((sEquiv.symm.trans iotaEquiv.symm : Shat ≃* NativeSporadic.B) t2DS) a :=
    babyTableIII.2 2 _ _ babyInv_two_t2DS ha
  exact @RootClassLarge.of_isConj NativeSporadic.B Units.instGroup _ _ hconj
    (@RootClassLarge.of_mulEquiv Shat NativeSporadic.B _ Units.instGroup
      (sEquiv.symm.trans iotaEquiv.symm) t2DS rootClassLarge_t2DS)

end CFSG.EvenSporadicStandard.HypOne.BabyHyp
