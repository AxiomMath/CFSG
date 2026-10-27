module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.RowFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.ReachGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm24Gen
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Co1
public import CFSG.Sporadic.Co1Block.TwoCData

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Co1Block
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Hyp


theorem co1_card_pinned : ∀ (Y : Type) [Group Y], IsSporadic Y .Co1 →
    Nat.card Y = 4157776806543360000 := by
  intro Y _ ⟨e⟩
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.Sporadic.Co1.card_Co1

theorem co1_up : UpFacts [] where
  fi23 _ h := absurd h List.not_mem_nil
  not_exc _ h := absurd h List.not_mem_nil
  odd _ h := absurd h List.not_mem_nil
  rank _ h := absurd h List.not_mem_nil

theorem co1_thm24 (lo : LieModelOrders) : ∀ s ∈ [TauCeti.SporadicName.Co1],
    s = .M ∨ (s ≠ .M ∧ Thm24Hex s) := by
  intro s hs
  rcases List.mem_singleton.1 hs with rfl
  refine Or.inr ⟨by decide, fun X _ hq hodd hX => thm24Hex_of_card lo (N := 4157776806543360000)
    co1_card_pinned (by norm_num)
    (factorial_div_two_ne_of_between (n₀ := 20) (by norm_num) (by norm_num)) X hq hodd hX⟩

theorem co1_fi23 : ∀ s ∈ [TauCeti.SporadicName.Co1] ++ [],
    Fi23Excl s := by
  intro s hs
  rcases List.mem_singleton.1 (by simpa using hs) with rfl
  exact fi23Excl_of_card co1_card_pinned (by norm_num)

theorem co1_sp_not_exc : ∀ s ∈ [TauCeti.SporadicName.Co1] ++ [], SporadicNotExc s := by
  intro s hs
  rcases List.mem_singleton.1 (by simpa using hs) with rfl
  exact sporadicNotExc_of_card co1_card_pinned (c := 2025957) (by norm_num) (by norm_num)
    (by norm_num)

end CFSG.EvenSporadicStandard.Induction
