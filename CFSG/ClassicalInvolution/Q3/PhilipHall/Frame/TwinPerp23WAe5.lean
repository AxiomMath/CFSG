module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23WFin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU4

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
open scoped commutatorElement




namespace W

open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc.AE5 CFSG.ClassicalInvolution.Asc77.Thompson

theorem p23_false_of_ae5 {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R}
    {t : Y} {K' Wg : Subgroup Y} {u e g : Y} (hc : P23Cfg n Y R S t K' Wg u e g)
    (hAE : SecAE R e 5) : False := by
  obtain ⟨I⟩ := hAE
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  have hc2 : IsPGroup 2 (Subgroup.zpowers e) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hc.data.he2
  have hperp : KPerp (Om R) (tightCore R) = {tightCore R, K'} :=
    hc.std.perp.perp.trans (twinSet_eq_pair hc.std.two hc.std.hK' hc.std.hne)
  have hs : CFSG.ClassicalInvolution.Q8P.Asc77.Hyp23Setting (Om R) (tightCore R) K' t :=
    ⟨CFSG.ClassicalInvolution.Q8P.ascStand_of_twinCore hC, hc.std.perp.disc, hz, hc.std.hK',
      hc.std.hne, hperp⟩
  obtain ⟨S₀, R₀, R', hWS, hR₀, -, hRS, -⟩ :=
    CFSG.ClassicalInvolution.Q8P.Asc77.T7D.exists_sylow_frame hs hc.std.hW hc.std.htW
  have hRD : R₀ ∈ DSet (Om R) Wg :=
    Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hc.std.hW hWS (mem_RSet_of_isSylow2In hK hR₀) hRS
  have hNe := normalizer_le_centralizer_e hc.data
  obtain ⟨eμ⟩ := hc.std.hS4
  exact false_of_ae5_mu hΩ h2 hc2 (p23_q8Section hc.std.perp hc.data.he2) I hc.std.hW
    (fun R' hR' => hR'.2.trans hNe) eμ hK hR₀ hRD hz hc.std.htW

theorem p23E4Ae5_proved (n : ℕ) : P23E4Ae5 n := by
  intro _ _ Y _ _ R S t K' Wg u e g hc _ hAE
  exact (p23_false_of_ae5 hc hAE).elim

end W

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
