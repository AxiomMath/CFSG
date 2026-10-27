module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_5_2M22Crit
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeReduction
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspM22Cent
public import CFSG.Quasithin.Background.SmithB45MatM22Cls
public import CFSG.Sporadic.Bridge.M22

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem isLocallyBalancedAbs_nativeM22 :
    IsLocallyBalancedAbs 3 2 NativeSporadic.M22 := by
  refine isLocallyBalancedAbs_three_two_of_oneOuter NativeSporadic.M22 m22Delta
    m22_delta_normalizes m22_delta_sq m22_center_eq_bot' m22_delta_outer m22_mulAut_card
    (fun u hu ho => ?_) (fun u hu ho => ?_) (fun x hx h3 => ?_)
  · rw [CFSG.Quasithin.H13.Ch4.I436.m22_inv_centralizer_card u hu ho]
    norm_num
  · rcases CFSG.Quasithin.H13.Ch4.I436.m22_outer_centralizer_card u hu ho with h | h <;>
      rw [h] <;> norm_num
  · have h := CFSG.Quasithin.B45Mat.M22.orderOf_mem_of_isPRegular x
      (show IsPRegular 2 x from Nat.coprime_two_right.2 hx)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    omega

theorem isLocallyBalancedAbs_M22 :
    IsLocallyBalancedAbs 3 2 (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M22).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  exact IsLocallyBalancedAbs.of_mulEquiv e.symm isLocallyBalancedAbs_nativeM22

end CFSG.HardMathSupport.Solomon.Coordinator
