module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ON7Wrap
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.Fi7Gen

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.Sporadic.Fi24 CFSG.RankThree.PartTwo.Sec4
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census

theorem fi7_sevenModel :
    SevenModel J 7 Fi7.Q7 Fi7.C7 Fi7.gens7 where
  line := Fi7.sevenLine_c
  syl := Fi7.Q7_sylow
  gens_top := Fi7.fi7_gens_top
  gens_good := Fi7.fi7_gens_good
  rankOK := Fi7.fi7_rankOK Fi7.fi7_order_four

theorem sporPlaneKill_Fi24Prime_seven
    (hOut : SporadicOuterLeTwo) : SporPlaneKill .Fi24Prime 7 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
  have b₀ : NativeSporadic.Carrier .Fi24Prime ≃* Spor .Fi24Prime := b
  have bX : ↥J ≃* Spor .Fi24Prime := fi24EquivJ.symm.trans b₀
  have hD : ∃ (Q : Subgroup ↥J) (z : ↥J) (gens : Set ↥J), SevenModel ↥J 7 Q z gens :=
    ⟨_, _, _, fi7_sevenModel⟩
  exact @sporPlaneKill_of_sevenModel hOut .Fi24Prime (by decide) ↥J (Subgroup.toGroup J)
    inferInstance bX hD _ _ b₀ offPair_Fi24Prime

theorem sporPair_Fi24Prime_seven
    (hOut : SporadicOuterLeTwo) : SporPair .Fi24Prime 7 :=
  sporPair_of_planeKill (sporPlaneKill_Fi24Prime_seven hOut)

end CFSG.HardMathSupport.Dickson.I271
