module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.E81Cent
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OuterPow
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Parts
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineSuz
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporSuz27

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Blueprint CFSG.Sporadic.SuzOddCore CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Item434SporE81
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem dvd_card_centralizer_suzM
    {s : suzM} (hs : orderOf s = 3) :
    81 ∣ Nat.card ↥(Subgroup.centralizer ({s} : Set suzM)) :=
  dvd_card_centralizer_of_e81Check suzE81 Certificates.certificate9458 rfl
    (by rw [show suzE81.qOrd = 2187 from rfl]; norm_num) Item434SporSuz.pg_mem
    Item434SporSuz.qOrd_eq hs

theorem sporadicOuterHolds_Suz_three :
    SporadicOuterHolds .Suz 3 := by
  intro S _ _ _ ⟨e⟩
  have e0 : S ≃* NativeSporadic.Suz := e
  refine noOuterFixesCentralizer_of_pow_dvd 81 ?_ ?_
  · intro σ hσ2 hσ H hH h81
    have hσ1 : σ ≠ 1 := fun h => hσ (h ▸ (innerAut S).one_mem)
    have hord : orderOf σ = 2 := orderOf_eq_prime hσ2 hσ1
    have hle : H ≤ fixedSubgroup σ := fun x hx => hH x hx
    have hdvd := h81.trans (Subgroup.card_dvd_of_le hle)
    rcases CFSG.SeitzReduction.SporadicRefine.suz_outer_card_fixedSubgroup e0 hord hσ with h | h
    · rw [h] at hdvd
      exact absurd hdvd (by norm_num)
    · rw [h] at hdvd
      exact absurd hdvd (by norm_num)
  · intro s hs
    have e' : S ≃* suzM := e0.trans suzEquivM
    rw [← card_centralizer_mulEquiv e' s]
    exact dvd_card_centralizer_suzM (by rw [MulEquiv.orderOf_eq]; exact hs)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
