module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.MultSporadic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.AtlasMain
public import CFSG.Sporadic.Bridge.Fi23Surj
public import CFSG.Sporadic.Bridge.Fi24Surj

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.RankThree.PartTwo.Sec4
  CFSG.RankThree.PartTwo.Sec4.Census CFSG.EvenSporadicStandard.Induction.Fi

theorem fi23Mult_of_sporadicMultipliers
    (hSM : SporadicMultipliers) : Fi23Mult := by
  intro X _ _ hq hX
  have h := card_center_dvd_of_sporadicMultipliers (s := .Fi23) hSM
    CFSG.Sporadic.Bridge.Fi23.nonempty_mulEquiv hq hX
  exact Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.1 (h.trans (by decide)))

theorem fi24Mult_of_sporadicMultipliers
    (hSM : SporadicMultipliers) : Fi24Mult := by
  intro X _ _ hq hX
  have h := (card_center_dvd_of_sporadicMultipliers (s := .Fi24Prime) hSM
    CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv hq hX).trans (by decide : _ ∣ 3)
  exact (Nat.Prime.odd_of_ne_two Nat.prime_three (by norm_num)).of_dvd_nat h

end CFSG.EvenSporadicStandard.Induction
