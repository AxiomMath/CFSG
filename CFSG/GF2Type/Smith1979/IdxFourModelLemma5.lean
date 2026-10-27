
module

public import CFSG.GF2Type.Smith1979.IdxFourModelLemma5Base

public import Certificates.Certificate17606

public section

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.IdxFour.Orb

theorem normal_two_subgroup_card_le_four
    {N : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (hN : N ≤ stabIn M0 w0)
    (hnorm : ∀ g ∈ stabIn M0 w0, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (h2 : IsPGroup 2 N) :
    Nat.card N ≤ 4 := by
  have hPS : stabIn E0 w0 ≤ stabIn M0 w0 := inf_le_inf_right _ E0_le_M0
  letI : MulAction ↥(stabIn E0 w0) OmegaTy := omegaAction _ hPS
  haveI : MulAction.IsPretransitive ↥(stabIn E0 w0) OmegaTy := ⟨fun x y => by
    obtain ⟨A, hA, hAx⟩ := Certificates.certificate17606 _ ((inOmega_iff _).1 x.2)
    obtain ⟨B, hB, hBy⟩ := Certificates.certificate17606 _ ((inOmega_iff _).1 y.2)
    refine ⟨⟨B * A⁻¹, genGrp_pGens_le (mul_mem hB (inv_mem hA))⟩, Subtype.ext ?_⟩
    change (B * A⁻¹) x.1 = y.1
    rw [LinearEquiv.mul_apply, ← hAx, inv_apply_apply, hBy]⟩
  have hodd : Odd (Nat.card OmegaTy) := by
    rw [card_InOmega]
    decide
  set Nn : Subgroup ↥(stabIn E0 w0) := (N ⊓ stabIn E0 w0).subgroupOf (stabIn E0 w0) with hNn
  haveI : Nn.Normal := ⟨fun n hn g => by
    rw [hNn, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hn ⊢
    refine ⟨?_, ?_⟩
    · exact hnorm g.1 (hPS g.2) n.1 hn.1
    · exact mul_mem (mul_mem g.2 n.2) (inv_mem g.2)⟩
  have hNn2 : IsPGroup 2 Nn := by
    refine IsPGroup.of_equiv ?_ (Subgroup.subgroupOfEquivOfLe (inf_le_right (a := N)
      (b := stabIn E0 w0))).symm
    exact h2.to_le inf_le_left
  have hfix := fixed_of_normal_pGroup (X := OmegaTy) hodd Nn hNn2
  have hbot : N ⊓ stabIn E0 w0 = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun n hn => ?_
    have hnP : n ∈ stabIn E0 w0 := hn.2
    have hn' : (⟨n, hnP⟩ : ↥(stabIn E0 w0)) ∈ Nn := by
      rw [hNn, Subgroup.mem_subgroupOf]
      exact hn
    refine eq_one_of_fix_e0Base (mem_stabIn.1 hnP).1 fun b hb => ?_
    have hbΩ : InOmega (vecOf b) := (inOmega_iff _).2 (by
      rw [codeOf_vecOf b.2]
      exact e0Base_inOmega b hb)
    have := congrArg Subtype.val (hfix _ hn' ⟨vecOf b, hbΩ⟩)
    refine Fin.ext ?_
    rw [Chain.codePerm_apply]
    change codeOf (n (vecOf b)) = b
    rw [show n (vecOf b) = vecOf b from this, codeOf_vecOf b.2]
  have hidx : (stabIn E0 w0).relIndex (stabIn M0 w0) = 4 := by
    have h := Subgroup.relIndex_mul_card (H := stabIn E0 w0) (K := stabIn M0 w0)
    rw [inf_of_le_left hPS, card_stabIn_E0_w0, card_stabIn_M0_w0] at h
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 25920) (h.trans (by norm_num))
  have h1 : (stabIn E0 w0 ⊓ N).relIndex N = (stabIn E0 w0).relIndex N :=
    Subgroup.inf_relIndex_right _ _
  have h3 : (stabIn E0 w0).relIndex N ≤ (stabIn E0 w0).relIndex (stabIn M0 w0) :=
    Subgroup.relIndex_le_of_le_right hN (by rw [hidx]; norm_num)
  rw [inf_comm, hbot, Subgroup.relIndex_bot_left] at h1
  omega

end CFSG.GF2Type.Smith1979.IdxFour
