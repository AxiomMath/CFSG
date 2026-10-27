module

public import CFSG.ClassicalInvolution.Q3.TL4StepAsm
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Proving.CentralOddFreeTwoGroup

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

section Cit3

theorem tightTwistAllTwin_at {n : ℕ} (h : PhilipHall.Frame.Thm1RTwinLiftSetEBelow n) :
    TightTwistAllTwin n := by
  intro _ _ Y _ _ hn R S t hd hc hE2 htw hall _ hE4
  have B := PhilipHall.QuaternionBridge.q8Bridge_of_twisted hd hc hE2 htw hall
  have := B.simple
  have hlt : Nat.card (Y ⧸ genFittingFitting Y) < n := hn ▸ B.quot.card_lt
  obtain ⟨L, -, -, -, -, -, hFc, hFL⟩ := htw
  have hN2 := PhilipHall.Proving.isPGroup_two_genFittingFitting hc.2.2 hFc
  have hNbot := PhilipHall.Proving.genFittingFitting_ne_bot_of_not_le hFL
  have ht1 : QuotientGroup.mk' (genFittingFitting Y) t ≠ 1 := by
    intro h1
    have := B.quot.datum.order
    rw [h1, orderOf_one] at this
    omega
  rcases h _ hlt _ _ _ B.quot.datum B.quot.cls.1 B.quot.cls.2.1
      (PhilipHall.Frame.oddCore_eq_bot_of_fstar B.nonab) B.quot.hyp B.aEmpty B.quot.twin with
    h1 | h2 | h3
  · exact absurd h1 (PhilipHall.Frame.not_tightInO2_of_fstar B.nonab ht1)
  · exact absurd (PhilipHall.QuaternionBridge.tightE4_of_exLie_quotient hN2 hNbot
      (h2.exLie B.nonab)) hE4
  · exact PhilipHall.QuaternionBridge.good_of_hasLift_twin hd B.central B.two B.not_mem
      (h3.hasLift B.quot.twin)

theorem tightPlusStep_of_parts' {n : ℕ} (hsmall : TightSmallBase) (hE : TightLargeEdgeS n)
    (hodd : OddLeafStep n) (hconn : ConnLeafStep n) (hE3 : E3LeafStep n)
    (h4 : PlusLeaf Thm4RBelow n) (hD2 : ThmD2StepR 3 n) (hD1 : ThmD1StepR 3 n)
    (h6 : Thm6StepR 3 n) (h5 : Thm5StepR 3 n) (htwin : TwinStepR 3 n) : TightPlusStep 3 n :=
  fun hA hP => tightPlusStep_of_parts (tightTwistAllTwin_at (hP.twin rfl)) hsmall hE hodd hconn
    hE3 h4 hD2 hD1 h6 h5 htwin hA hP

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
