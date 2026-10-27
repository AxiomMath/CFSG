module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.FactsGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.RowFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm24Gen
public import CFSG.Sporadic.Fi22.Simple
public import CFSG.Sporadic.Fi24.Simple

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction.Fi

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.Induction.Hyp

section Pinned

theorem pinCard22 : Nat.card (Carrier .Fi22) = 64561751654400 := CFSG.Sporadic.Fi22.card_Fi22

theorem pinCard23 : Nat.card (Carrier .Fi23) = 4089470473293004800 :=
  CFSG.Sporadic.Fi23.card_Fi23

theorem pinCard24 : Nat.card (Carrier .Fi24Prime) = 1255205709190661721292800 :=
  CFSG.Sporadic.Fi24.card_Fi24prime

theorem pinSimple23 : IsSimpleGroup (Carrier .Fi23) := CFSG.Sporadic.Fi23.isSimpleGroup_Fi23

theorem pinNotExc22 : SporadicNotExc .Fi22 :=
  fiSporadicNotExc_of_card (c := 50543) pinCard22 (by norm_num) (by norm_num) (by norm_num)

theorem pinNotExc23 : SporadicNotExc .Fi23 :=
  fiSporadicNotExc_of_card (c := 2014801) pinCard23 (by norm_num) (by norm_num) (by norm_num)

theorem pinNotExc24 : SporadicNotExc .Fi24Prime :=
  fiSporadicNotExc_of_card (c := 135909026) pinCard24 (by norm_num) (by norm_num) (by norm_num)

theorem pinFi23Excl22 : Fi23Excl .Fi22 :=
  fi23Excl_of_card_ne pinSimple23 pinCard23 (by norm_num) pinCard22 (by norm_num)

theorem pinFi23Excl24 : Fi23Excl .Fi24Prime :=
  fi23Excl_of_card_ne pinSimple23 pinCard23 (by norm_num) pinCard24 (by norm_num)

theorem pinThm24Hex22 (lo : LieModelOrders) : Thm24Hex .Fi22 :=
  fun X _ hq hodd hX => thm24Hex_of_card lo (fun _ _ h => card_of_isSporadic pinCard22 h)
    (by norm_num) (fun n => factorial_div_two_ne_of_between (n₀ := 16)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial]) n) X hq hodd hX

theorem pinThm24Hex23 (lo : LieModelOrders) : Thm24Hex .Fi23 :=
  fun X _ hq hodd hX => thm24Hex_of_card lo (fun _ _ h => card_of_isSporadic pinCard23 h)
    (by norm_num) (fun n => factorial_div_two_ne_of_between (n₀ := 20)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial]) n) X hq hodd hX

theorem pinThm24Hex24 (lo : LieModelOrders) : Thm24Hex .Fi24Prime :=
  fun X _ hq hodd hX => thm24Hex_of_card lo (fun _ _ h => card_of_isSporadic pinCard24 h)
    (by norm_num) (fun n => factorial_div_two_ne_of_between (n₀ := 24)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial]) n) X hq hodd hX

end Pinned

end CFSG.EvenSporadicStandard.Induction.Fi
