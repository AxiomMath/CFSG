module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428Facts
import CFSG.LocalAnalysis.GLTheoremA.CatA.I112Types
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TCAll
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.ScopeBInputs
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1131

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T1428

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Tables.Census
open CFSG.LocalAnalysis.GLTheoremA


theorem t1428TypeFact_holds
    : T1428TypeFact := by
  intro p hp hp2 Ω _ _ hΩ B L hB hr hL hnL
  obtain ⟨rfl, -, htype⟩ :=
    i112_types_of_isKGroup tables112_holds tableL2_unconditional tables112Types_holds
      hp hp2 hΩ hB hr hL hnL
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 L) :=
    isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hL
  refine ⟨rfl, ?_⟩
  rcases htype with hL2 | h6 | h7 | h22 | hSL | hSU
  ·
    have hodd : IsLTwoOddPow (PQuot 3 L) := hL2
    have hL2' : IsL2TwoPowOdd (PQuot 3 L) := isL2TwoPowOdd_of_isLTwoOddPow hodd
    have hcent : Subgroup.center (PQuot 3 L) = ⊥ := IsL2TwoPowOdd.center_eq_bot hL2'
    have eQ : PSimple 3 L ≃* PQuot 3 L :=
      (QuotientGroup.quotientMulEquivOfEq hcent).trans QuotientGroup.quotientBot
    exact (catalogIs_congr eQ).2 (catalogIs_weakExcIndex_of_isL2TwoPowOdd hL2')
  all_goals
    obtain ⟨i, hi, he⟩ := (isExcShape_of_types hq (by tauto)).2
    exact ⟨i, Or.inl hi, he⟩

theorem t1428NormFact_holds
    : T1428NormFact := by
  intro p hp hp2 Ω _ _ hΩ B K hB hL hnL
  have hr : GLATwoLocalRank p Ω ≤ CFSG.Open.pRank p B :=
    CFSG.SectionRank.le_pRank hp.one_lt le_rfl hB.1 hB.2.1
  obtain ⟨rfl, hrel, htype⟩ :=
    i112_types_of_isKGroup tables112_holds tableL2_unconditional tables112Types_holds
      hp hp2 hΩ hB.1 hr hL hnL
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 K) :=
    isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hL
  have hnL2 : ¬ IsLTwoOddPow (barOf 3 K) := fun hL2 =>
    (kernel11_3a_of_tables tables112_holds tableL2_unconditional) Ω hΩ B hB K hL hnL hrel
      (isL2TwoPowOdd_of_isLTwoOddPow hL2)
  refine ⟨rfl, ?_⟩
  rcases htype with h | h6 | h7 | h22 | hSL | hSU
  · exact absurd h hnL2
  all_goals exact isExcShape_of_types hq (by tauto)

end CFSG.LocalAnalysis.GLTheoremA.T1428

end
