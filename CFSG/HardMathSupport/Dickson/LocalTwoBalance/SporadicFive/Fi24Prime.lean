module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10Red
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalTwoFrontier
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.SporadicFive.Fi24PrimeAux.OPrimeR
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.SporadicFive.Fi24PrimeAux.AutModel

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Sporadic.Fi24 (R J JR jR)

theorem sporadicTwoBalanceFive_Fi24Prime :
    SporadicTwoBalanceFive .Fi24Prime := by
  rintro S _ _ hsimple hnab ⟨e⟩
  obtain ⟨bF⟩ := CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
  obtain ⟨θ⟩ : Nonempty (S ≃* ↥JR) := ⟨((e.trans bF.symm).trans
    CFSG.Sporadic.Fi24.fi24EquivJ).trans
    (Subgroup.subgroupOfEquivOfLe CFSG.Sporadic.Fi24.J_le_R).symm⟩
  have hcen : Subgroup.center S = ⊥ := center_eq_bot_of_isSimpleGroup hnab
  have hout : Nat.card (Outer S) ≤ 2 :=
    Fi24PrimeAux.card_outer_le_two hcen (Fi24PrimeAux.card_mulAut_of_mulEquiv θ)
  refine isLocallyBalancedAbs_two_of_autModel Nat.prime_five (by norm_num)
    Fi24PrimeAux.fi24_autModel θ hcen hout ?_
  intro E hE hEc
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨d, hdE, hd1⟩ : ∃ d ∈ E, d ≠ 1 := by
    by_contra h
    have hbot : E = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      by_contra hx1
      exact h ⟨x, hx, hx1⟩
    rw [hbot, Subgroup.card_bot] at hEc
    norm_num at hEc
  have hd5 : orderOf d = 5 := orderOf_eq_prime (hE.2 d hdE) hd1
  refine ⟨d, hdE, hd1, ?_⟩
  rw [inf_top_eq]
  exact Fi24PrimeAux.oPrimeCoreTrivialAt_R_five _ (by rw [Subgroup.orderOf_coe, hd5])

end CFSG.HardMathSupport.Dickson.LocalTwoBalance
