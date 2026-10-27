module

public import CFSG.ClassicalInvolution.Q3.Q3MFODSpin
public import CFSG.ClassicalInvolution.Q3.Q3OTDict
public import CFSG.ClassicalInvolution.Q3.Q3OTCplx
public import CFSG.ClassicalInvolution.Q3.Q3NMOrth
public import CFSG.ClassicalInvolution.Q3.Q3PPFundFix
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerBlocks
public import CFSG.ClassicalInvolution.Q3.Q3NMM11
public import CFSG.ClassicalInvolution.Q3.Q3NMSl23

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MFOD

open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Models.Transfer
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Q3.Q3OT
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Main

variable {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q : QuadraticForm F (ι → F)}

theorem fixedOddFreeFund_of_spin3 [Finite (spinGroup Q)] [Group.IsPerfect (spinGroup Q)]
    (hF3 : Nat.card F = 3) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 6 ≤ Module.finrank F (ι → F)) (hrange : (spinAction Q).range = elementaryGroup Q)
    (hZ : CenterScalar Q) (hker2 : ∀ x ∈ (spinAction Q).ker, x * x = 1)
    (hOE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
      elementaryGroup Q)
    (hlift : LiftSim Q (QuotientGroup.mk' (Subgroup.center (spinGroup Q))))
    (hquasi : CFSG.Open.IsQuasisimple (spinGroup Q))
    (hZ2 : IsPGroup 2 (Subgroup.center (spinGroup Q)))
    {𝓕 : Set (Subgroup (spinGroup Q))}
    (cq : CentralQuot3 (spinAction Q) 𝓕 (fundSet Q) (scalars F (ι → F)))
    (hIII : ∀ (α : MulAut (spinGroup Q)) (a : (ι → F) ≃ₗ[F] (ι → F)), a * a = 1 →
      (∀ v, Q (a v) = -Q v) → (∀ x, spinAction Q (α x) = a * spinAction Q x * a⁻¹) →
      oddCoreIn (fixedSubgroup (autToCentralQuotient (spinGroup Q) α)) = ⊥) :
    CFSG.ClassicalInvolution.Q3.Q3PP.FixedOddFreeFund (⟨spinGroup Q, 𝓕⟩ : CompData) := by
  classical
  intro ρ hρ2 ⟨R, hR, hρR⟩
  have : Nontrivial (ι → F) := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  have hZ3 := center_no_three hF3 hrange hZ hker2
  obtain ⟨α, a, μ, fr, hμ, hsim, hα, hαρ, hα2, hLa⟩ :=
    exists_sim_data3 hF3 hZ3 hlift cq ρ hρ2 hR hρR
  have hρeq : ρ = autToCentralQuotient (spinGroup Q) α := by
    refine MulEquiv.ext fun xb => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
    rw [autToCentralQuotient_mk, hαρ]
  rw [hρeq]
  have hcomm : ∀ h ∈ elementaryGroup Q, a * a * h = h * (a * a) := by
    intro h hh
    rw [← hrange] at hh
    obtain ⟨s, rfl⟩ := hh
    have hαα : α (α s) = s := by
      have := congrArg (fun m : MulAut (spinGroup Q) => m s) hα2
      simpa using this
    have e : spinAction Q s = a * (a * spinAction Q s * a⁻¹) * a⁻¹ := by
      rw [← hα s, ← hα (α s), hαα]
    calc a * a * spinAction Q s
        = (a * (a * spinAction Q s * a⁻¹) * a⁻¹) * (a * a) := by group
      _ = spinAction Q s * (a * a) := by rw [← e]
  have hlift' : ∀ (g : (ι → F) ≃ₗ[F] (ι → F)) (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q),
      (∀ x, spinAction Q (α x) = g * spinAction Q x * g⁻¹) →
      oddCoreIn (fixedSubgroup (autToCentralQuotient ↥(elementaryGroup Q) (conjE Q g hgO))) = ⊥ →
      oddCoreIn (fixedSubgroup (autToCentralQuotient (spinGroup Q) α)) = ⊥ :=
    fun g hgO hg hN => oddCoreIn_fixed_of_lift hrange (θ := MonoidHom.id (spinGroup Q))
      Function.surjective_id (by rw [MonoidHom.ker_id]; exact bot_le) α α (fun s => rfl) hgO hg hN
  rcases sim_cases hF3 hQ (by omega) fr hμ hsim hLa hcomm with
    ⟨hμ1, haa⟩ | ⟨hμ1, haa⟩ | ⟨hμ1, haa⟩
  ·
    have haO : a ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
      rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
      intro v
      rw [hsim, hμ1, one_mul]
    by_cases hs : a ∈ scalars F (ι → F)
    ·
      obtain ⟨c, hc⟩ := mem_scalars.mp hs
      have hcomm_a : ∀ g : (ι → F) ≃ₗ[F] (ι → F), a * g = g * a := fun g => by
        refine LinearEquiv.ext fun v => ?_
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hc, hc, map_smul]
      have hone : autToCentralQuotient (spinGroup Q) α = 1 := by
        refine MulEquiv.ext fun xb => ?_
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
        rw [autToCentralQuotient_mk, MulAut.one_apply]
        refine QuotientGroup.eq.mpr (ker_spinAction_le_center Q ?_)
        rw [MonoidHom.mem_ker, map_mul, map_inv, hα, hcomm_a (spinAction Q x), mul_inv_cancel_right,
          inv_mul_cancel]
      rw [hone]
      have hf : fixedSubgroup (1 : MulAut (spinGroup Q ⧸ Subgroup.center (spinGroup Q))) = ⊤ := by
        ext x
        simp [mem_fixedSubgroup_iff]
      rw [hf]
      have h := CFSG.ClassicalInvolution.Q3.oddCoreIn_range_eq_bot_of_isQuasisimple
        (QuotientGroup.mk' (Subgroup.center (spinGroup Q))) hquasi hZ2
        (by rw [QuotientGroup.ker_mk'])
      rwa [MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h
    · exact hlift' a haO hα
        (oddCoreIn_fixed_eq_bot_of_involution hF3 hQ (by omega) haO haa hs)
  ·
    have haO : a ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
      rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
      intro v
      rw [hsim, hμ1, one_mul]
    exact hlift' a haO hα (oddCoreIn_fixed_eq_bot_of_cplx hF3 hQ hdim hOE haO haa)
  ·
    exact hIII α a haa (fun v => by rw [hsim, hμ1]; ring) hα

end Main

end CFSG.ClassicalInvolution.Q3.Q3MFOD
