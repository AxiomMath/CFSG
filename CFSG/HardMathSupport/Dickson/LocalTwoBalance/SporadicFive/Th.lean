module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10Red
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalTwoFrontier
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.SporadicGammaPairs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThFive
public import CFSG.Sporadic.Bridge.ThSurj
public import CFSG.Sporadic.ThSchreier.NodeFullAutomorphism
public import Certificates.Certificate1020
public import Certificates.Certificate1021
public import Certificates.Certificate1022
public import Certificates.Certificate2309
public import Certificates.Certificate2311
public import Certificates.Certificate2313
public import Certificates.Certificate2314
public import Certificates.Certificate2315
public import Certificates.Certificate2317
public import Certificates.Certificate2321
public import Certificates.Certificate2322
public import Certificates.Certificate2323
public import Certificates.Certificate2324
public import Certificates.Certificate2325
public import Certificates.Certificate9131
public import Certificates.Certificate9220
public import Certificates.Certificate10088
public import Certificates.Certificate10089
public import Certificates.Certificate10090
public import Certificates.Certificate10091
public import Certificates.Certificate10092
public import Certificates.Certificate16949
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Setup

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.LocalTwo

theorem sporadicTwoBalanceFive_Th :
    SporadicTwoBalanceFive .Th := by
  rintro S _ _ hsimple hnab ⟨e⟩
  obtain ⟨e'⟩ := CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
  let f : S ≃* Blueprint.NativeSporadic.Th := e.trans e'.symm
  have hinnTh : innerAut Blueprint.NativeSporadic.Th = ⊤ :=
    CFSG.Sporadic.ThSchreier.inner_Th
  have hinn : innerAut S = ⊤ :=
    @innerAut_eq_top_of_mulEquiv S Blueprint.NativeSporadic.Th _ _ f hinnTh
  refine isLocallyBalancedAbs_two_of_plane_witness (center_eq_bot_of_isSimpleGroup hnab) hinn ?_
  intro E hE hEc
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨d, hdE, hd1⟩ : ∃ d ∈ E, d ≠ 1 := by
    by_contra h
    push_neg at h
    have hbot : E = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      exact h
    rw [hbot, Subgroup.card_bot] at hEc
    norm_num at hEc
  have hd5 : orderOf d = 5 := orderOf_eq_prime (hE.2 d hdE) hd1
  exact ⟨d, hdE, hd1, sporadicOPrimeHolds_Th_five S ⟨f⟩ d hd5⟩

end CFSG.HardMathSupport.Dickson.LocalTwoBalance
