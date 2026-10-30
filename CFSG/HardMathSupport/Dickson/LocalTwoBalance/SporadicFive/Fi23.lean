module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10Red
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalTwoFrontier
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23FiveSylow

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.LocalTwo

theorem sporadicTwoBalanceFive_Fi23 :
    SporadicTwoBalanceFive .Fi23 := by
  rintro S _ _ hsimple hnab ⟨e⟩
  obtain ⟨e'⟩ := CFSG.Sporadic.Bridge.Fi23.nonempty_mulEquiv
  let f : S ≃* Blueprint.NativeSporadic.Fi23 := e.trans e'.symm
  have hinnF : innerAut Blueprint.NativeSporadic.Fi23 = ⊤ :=
    CFSG.Sporadic.FischerOddCore.inner_fi23_eq_top
  have hinn : innerAut S = ⊤ :=
    @innerAut_eq_top_of_mulEquiv S Blueprint.NativeSporadic.Fi23 _ _ f hinnF
  refine isLocallyBalancedAbs_two_of_plane_witness (center_eq_bot_of_isSimpleGroup hnab) hinn ?_
  intro E hE hEc
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨d, hdE, hd1⟩ : ∃ d ∈ E, d ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : E = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      exact h
    rw [hbot, Subgroup.card_bot] at hEc
    norm_num at hEc
  have hd5 : orderOf d = 5 := orderOf_eq_prime (hE.2 d hdE) hd1
  exact ⟨d, hdE, hd1, sporadicOPrimeHolds_Fi23_five S ⟨f⟩ d hd5⟩

end CFSG.HardMathSupport.Dickson.LocalTwoBalance
