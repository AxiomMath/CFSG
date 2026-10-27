module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.TriXSplit
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.TriXPlus
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.LongShortFixed

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.TriXPlus

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.Fischer CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartTwo.Sec19 CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c

theorem triXNoGCentUniPlanesAt_one :
    TriXNoGCentUniPlanesAt 1 := by
  intro ℓ f hℓ hℓ2 hℓ3 hf hq K _ _ hK σ hσ E x hE hcard hout hnG hncent hx3 hx1 hcx hX hbp
  have hK2 : ringChar K ≠ 2 := triOdd_ringChar_ne_two hℓ hℓ2 hf hK
  have hq5 : 5 ≤ ℓ ^ f := by
    have h5 : 5 ≤ ℓ := by
      by_contra h
      have h2 := hℓ.two_le
      interval_cases ℓ
      · exact hℓ2 rfl
      · exact hℓ3 rfl
      · norm_num at hℓ
    calc 5 ≤ ℓ := h5
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf
  exact uniPlaneClosure_eq_top_of_fixedSub ℓ f hℓ hℓ2 hℓ3 hf hq hK σ hσ E x hE hcard hout hnG
    hncent hx3 hx1 hcx hX hbp
    (fun hσ3 H hL hx =>
      CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.LongShort.fixedSub_le_of_longSub_short
        hσ3 hK2 hq5 hK hσ H hL hx)

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.TriXPlus
