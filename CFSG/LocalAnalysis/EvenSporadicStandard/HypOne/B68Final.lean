module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.B68Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.B68Cap
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.BNoOrder68

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HypOne.BabyHyp

open CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS CFSG.Monster.Existence

theorem babyArith : B68.Arith babyCentOrder babyOrbitSize where
  inj := babyCentOrder_injective
  dvd17 k := by
    fin_cases k <;> simp [babyCentOrder]
  dvd0 := by norm_num [babyCentOrder]
  nsq := by norm_num [babyCentOrder]
  dvd_sz2 := by norm_num [babyOrbitSize]
  cop_sz1 := by norm_num [babyOrbitSize]
  ne_sz1 := by norm_num [babyOrbitSize]
  idx := by norm_num [babyCentOrder, babyOrbitSize]

theorem babyNoOrder68 : BabyNoOrder68 :=
  B68.no_order_sixtyEight (G := B) babyArith babyTableIII babyTableIV B68.cap_baby
    ⟨babyRep 1, babyInv_zero_babyRep_one⟩

end CFSG.EvenSporadicStandard.HypOne.BabyHyp
