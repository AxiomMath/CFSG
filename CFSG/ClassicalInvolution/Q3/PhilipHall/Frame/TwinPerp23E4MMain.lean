module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMuPf2P23
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23E4MFrame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23E4MGlue
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23E4MSp6
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23WOrd2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23WOrd1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf62E4Model

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected

namespace E4M



theorem p23E4Mu_of_models (hT : TwinThmE.T4Supply)
    (hD4 : TwinCentRes.ModelFactD42) (hO8 : TwinDisc.ExitE4.E4O8TwinModel)
    (hSp : E4Sp6FrameModel) (n : ℕ) : P23E4Mu n := by
  intro hcit hP Y _ _ R S t K' Wg u e g hc _ _
  obtain ⟨hedge, htw, hdich⟩ := e_exit_frame4 (hT n hcit hP) hc
  have hthree := W.p23_three_dvd_e hc
  have htrans : ∀ K ∈ TwinDisc.secFam (Om R) e, ∀ L ∈ TwinDisc.secFam (Om R) e,
      ∃ x : SecQ R e, conjSub x K = L := by
    rcases hdich with h | ⟨k, hk⟩
    · exact h
    · exfalso
      rw [hk] at hthree
      exact absurd (Nat.prime_three.dvd_of_dvd_pow hthree) (by norm_num)
  have hS := p23_q8Section hc.std.perp hc.data.he2
  have hodd := oddCent_exit_gen2 hD4 hcit hP hc.std.perp hc.data.he2 hc.data.he1 htrans hedge htw
  obtain ⟨A, A', B, z, u₁, u₂, τ, ε₀, hF, hnb, -⟩ := e_frame_sec hc
  exact secMuExcl_of_frame hO8 hSp hS htrans hodd hF hnb

theorem p23E4Mu_proved
    (hT : TwinThmE.T4Supply) (n : ℕ) : P23E4Mu n :=
  p23E4Mu_of_models hT TwinCentRes.modelFactD42_of_cert TwinDisc.e4O8TwinModel_of_certs
    e4Sp6FrameModel_of_certs n

end E4M

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
