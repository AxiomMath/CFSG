module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8PhiAE
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6bCover
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf7Distinct
public import CFSG.ClassicalInvolution.Q3.TL4AECoverB

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



section AE

variable {n : ℕ}

theorem p23E8UEComm_proved : P23E8UEComm n := by
  intro _ _ Y _ _ R S t K' W u e g hc hAE m hm
  classical
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hu2
  obtain ⟨R₁, R₁', -, -, hR₁, hR₁', hRD, hR'D, -, -, -, -, -, -, -⟩ := e_decomp hc
  have hNe := normalizer_le_centralizer_e hd
  have hR₃u := conj_cent_u hc (hRD.2.trans hNe) (fun x hx => Subgroup.mem_centralizer_singleton_iff.mp
    (le_centralizer_of_unique hz (hR₁.1 hx)))
  have hR₃'u := conj_cent_u hc (hR'D.2.trans hNe) (fun x hx => Subgroup.mem_centralizer_singleton_iff.mp
    (le_centralizer_of_unique hz' (hR₁'.1 hx)))
  have hJ₁Ω : conjSub g (tightCore R) ∈ Om R := hΩ.conjInvariant g _ hK
  have hJ₂Ω : conjSub g K' ∈ Om R := hΩ.conjInvariant g _ hc.std.hK'.1
  have hJ₁ : conjSub g (tightCore R) ∈ tqMembers3 (Om R) u :=
    ⟨hJ₁Ω, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₁Ω ⟨conjSub g R₁, hR₁.conj g, hR₃u⟩⟩
  have hJ₂ : conjSub g K' ∈ tqMembers3 (Om R) u :=
    ⟨hJ₂Ω, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₂Ω ⟨conjSub g R₁', hR₁'.conj g, hR₃'u⟩⟩
  have hτ₁ : IsUniqueInvolution (conjSub g (tightCore R)) (u * e) := by
    rw [← hd.hgt]; exact hz.conj g
  have hτ₂ : IsUniqueInvolution (conjSub g K') (u * e) := by
    rw [← hd.hgt]; exact hz'.conj g
  have hne₂ : conjSub g K' ≠ conjSub g (tightCore R) := by
    intro he
    apply hc.std.hne
    have := congrArg (conjSub g⁻¹) he
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
  have hS := TwinPerpV3.layer_q8Section hc.std.perp hd.hu2
  obtain ⟨I⟩ := hAE
  obtain ⟨hC₁, hY₁, hU₁⟩ := isUniqueInvolution_secImg hΩ hc2 hJ₁ hτ₁
  obtain ⟨_hC₂, _hY₂, hU₂⟩ := isUniqueInvolution_secImg hΩ hc2 hJ₂ hτ₂
  have hH : TL4.AECoverHyp I :=
    TwinPerpV3.A6b.aeCoverHyp_of_twins (by norm_num) (by norm_num) hS I (secImg_mem_secFam hJ₁)
      (secImg_mem_secFam hJ₂) (TwinPerpV3.secImg_ne_of_twin hΩ hc2 hJ₂ hJ₁ hne₂ hτ₂ hτ₁) hU₁ hU₂
  have hmu : m * u * m⁻¹ = u := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hm, mul_inv_cancel_right]
  have hJm : conjSub m (conjSub g (tightCore R)) ∈ tqMembers3 (Om R) u := by
    refine ⟨hΩ.conjInvariant m _ hJ₁.1, ?_⟩
    have h := trivialOnQuot_conjSub hJ₁.2 m
    rwa [hmu] at h
  have hτm : IsUniqueInvolution (conjSub m (conjSub g (tightCore R))) (m * (u * e) * m⁻¹) :=
    hτ₁.conj m
  obtain ⟨hCm, hYm, hUm⟩ := isUniqueInvolution_secImg hΩ hc2 hJm hτm
  have hcm := TL4.AECov.comm_of_isUniqueInvolution I (by norm_num) hH.card hH.conj_mem hH.label_inj
    hH.twin_z (secImg_mem_secFam hJ₁) (secImg_mem_secFam hJm) hU₁ hUm
  set H := coreHull (Om R) u with hHdef
  set a : ↥H := ⟨⟨u * e, hC₁⟩, hY₁⟩ with ha
  set b : ↥H := ⟨⟨m * (u * e) * m⁻¹, hCm⟩, hYm⟩ with hb
  have hab : a * b * a⁻¹ * b⁻¹ ∈ classicalInvolutionOddCore ↥H := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, QuotientGroup.mk_mul, hcm, mul_inv_cancel_right, mul_inv_cancel]
  exact oddCore_coreHull_le hΩ hc2 hab

theorem p23E8Phi_of_thm4 (hT : Thm4RTwinBelow 3 n) : P23E8Phi n :=
  p23E8Phi_of_comm hT p23E8UEComm_proved

end AE

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
