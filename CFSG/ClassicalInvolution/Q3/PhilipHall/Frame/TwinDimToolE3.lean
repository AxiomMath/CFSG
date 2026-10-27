module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimToolE2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimTool

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

section Dim

variable {n : ℕ}

theorem p23E4Dim (n : ℕ) : P23E4Dim n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno D hcard tag k d ε hort hcis
  obtain ⟨A, A', B, z, u₁, u₂, τ, ε₀, hfr, hdisc⟩ := e_frame hP hc hno
  have hS := p23_q8Section hc.std.perp hc.data.he2
  have hlt := secQ_card_lt hc.std.perp hc.data.he1
  obtain ⟨-, hl, -⟩ := lifts_of_noExit hP hlt hS hno
  have hΛ : HypOmegaModU (.sl2 3 1) (liftFam (TwinDisc.secFam (Om R) e)) :=
    hypOmegaModU_liftFam hS.hyp.conjInvariant
  have hgen : omegaGen (liftFam (TwinDisc.secFam (Om R) e)) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← hS.gen]
    refine iSup₂_le fun J hJ => ?_
    obtain ⟨L, u', hL⟩ := hl J hJ
    exact hL.le_sat.trans (le_omegaGen (satU_mem_liftFam hJ hL))
  obtain ⟨h6, hε⟩ := TwinDimTool.dimOfTwinFrame hΛ hgen D hcard ⟨0, by omega⟩ hort hcis hdisc hfr
  exact ⟨h6, by rw [hε]; decide⟩

end Dim

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
