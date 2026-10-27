module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017BFiveB
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017BFiveInv
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M5Crit
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017J3McL

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Blueprint


theorem twoRankLe_five_B_of_fiveBPure
    (h : BabyFiveBPureFact) : TwoRankLe 5 .B 2 := by
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  have hcrit : GLATwoLocalRank 5 NativeSporadic.B ≤ 2 := by
    refine H1016M5.twoLocalRankCriterion_holds NativeSporadic.B 5 2 4 Nat.prime_five
      (by norm_num) (fun j hj0 hj4 => by interval_cases j <;> decide) ?_ ?_
    · exact card_le_of_involution_B
    · exact false_of_five_two_four_B h
  refine twoRankLe_of_model (X := NativeSporadic.B) Nat.prime_five ?_ fun K _ _ ⟨φ⟩ => ?_
  · exact CFSG.Sporadic.Bridge.B.nonempty_mulEquiv
  · rw [← CFSG.HardMathSupport.Timmesfeld.Tables.Census.glaTwoLocalRank_congr (by norm_num) φ]
    exact hcrit

end CFSG.LocalAnalysis.GLTheoremA.H1017
