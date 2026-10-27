module

public import CFSG.GF2Type.Smith1979.IdxFourModelLemma5Base
public import Certificates.Certificate17606

public section

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.IdxFour.Orb

theorem normal_two_subgroup_stab_E0_eq_bot
    {P : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (hP : P ≤ stabIn E0 w0)
    (hnorm : ∀ g ∈ stabIn E0 w0, ∀ n ∈ P, g * n * g⁻¹ ∈ P) (h2 : IsPGroup 2 P) : P = ⊥ := by
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
  set Nn : Subgroup ↥(stabIn E0 w0) := P.subgroupOf (stabIn E0 w0) with hNn
  haveI : Nn.Normal := ⟨fun n hn g => by
    rw [hNn, Subgroup.mem_subgroupOf] at hn ⊢
    exact hnorm g.1 g.2 n.1 hn⟩
  have hNn2 : IsPGroup 2 Nn := IsPGroup.of_equiv h2 (Subgroup.subgroupOfEquivOfLe hP).symm
  have hfix := fixed_of_normal_pGroup (X := OmegaTy) hodd Nn hNn2
  refine (Subgroup.eq_bot_iff_forall _).2 fun n hn => ?_
  have hnP : n ∈ stabIn E0 w0 := hP hn
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

end CFSG.GF2Type.Smith1979.IdxFour
