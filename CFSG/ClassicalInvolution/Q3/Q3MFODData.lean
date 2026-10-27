module

public import CFSG.ClassicalInvolution.Q3.Q3MFODSpin
public import CFSG.ClassicalInvolution.Q3.Q3MFODSimE
public import CFSG.ClassicalInvolution.Q3.Q3OTCplx
public import CFSG.ClassicalInvolution.Q3.Q3NMOrth
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerBlocks
public import CFSG.ClassicalInvolution.Q3.Q3OTDict

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MFOD

open Matrix CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Models.Transfer
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Q3.Q3OT
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Data

variable {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q : QuadraticForm F (ι → F)}

theorem exists_sim_of_mat3 (hF3 : Nat.card F = 3) (α : MulAut (spinGroup Q))
    (h : ∃ (A : GL ι F) (φ : F ≃+* F) (μ : Fˣ),
      (∀ v : ι → F, Q (A.val *ᵥ (fun i => φ (v i))) = μ * φ (Q v)) ∧
        ∀ x, spinMatrix Q (α x) = A * glFieldEquiv ι φ (spinMatrix Q x) * A⁻¹) :
    ∃ (a : (ι → F) ≃ₗ[F] (ι → F)) (μ : F), μ ≠ 0 ∧ (∀ v, Q (a v) = μ * Q v) ∧
      ∀ x, spinAction Q (α x) = a * spinAction Q x * a⁻¹ := by
  obtain ⟨A, φ, μ, hsim, hmat⟩ := h
  have hφ := ringEquiv_eq_refl_of_card_three hF3 φ
  subst hφ
  have hmat' : ∀ x, spinMatrix Q (α x) = A * spinMatrix Q x * A⁻¹ := fun x => by
    rw [hmat x, glFieldEquiv_refl]
  refine ⟨glLin A, (μ : F), μ.ne_zero, ?_, ?_⟩
  · intro v
    have := hsim v
    simpa [glLin_apply] using this
  · intro x
    rw [← glLin_spinMatrix, hmat', map_mul, map_mul, map_inv, glLin_spinMatrix]

theorem oddCoreIn_fixed_of_sim_data [Finite (spinGroup Q)] [Group.IsPerfect (spinGroup Q)]
    (hF3 : Nat.card F = 3) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 6 ≤ Module.finrank F (ι → F)) (hrange : (spinAction Q).range = elementaryGroup Q)
    (hEq : elementaryGroup Q = ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hquasi : CFSG.Open.IsQuasisimple (spinGroup Q))
    (hZ2 : IsPGroup 2 (Subgroup.center (spinGroup Q)))
    (α : MulAut (spinGroup Q)) {a : (ι → F) ≃ₗ[F] (ι → F)} {μ : F} (fr : OFrame Q) (hμ : μ ≠ 0)
    (hsim : ∀ v, Q (a v) = μ * Q v) (hα : ∀ x, spinAction Q (α x) = a * spinAction Q x * a⁻¹)
    (hα2 : α * α = 1) (hLa : ∀ A : SL(2, F), a * fr.La A = fr.La A * a)
    (hIII : a * a = 1 → ∀ (hμ' : (-1 : F) ≠ 0) (hg' : ∀ v, Q (a v) = (-1 : F) * Q v),
      oddCoreIn (fixedSubgroup (autToCentralQuotient ↥(elementaryGroup Q)
        (conjES Q hEq hμ' hg'))) = ⊥) :
    oddCoreIn (fixedSubgroup (autToCentralQuotient (spinGroup Q) α)) = ⊥ := by
  classical
  have : Nontrivial (ι → F) := Module.nontrivial_of_finrank_pos (R := F) (by omega)
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
  have hkerle : (MonoidHom.id (spinGroup Q)).ker ≤ Subgroup.center (spinGroup Q) := by
    rw [MonoidHom.ker_id]
    exact bot_le
  have hlift' : ∀ κ : MulAut ↥(elementaryGroup Q),
      (∀ s, (κ ⟨spinAction Q s, by rw [← hrange]; exact ⟨s, rfl⟩⟩ : ↥(elementaryGroup Q)) =
        ⟨spinAction Q (α s), by rw [← hrange]; exact ⟨α s, rfl⟩⟩) →
      oddCoreIn (fixedSubgroup (autToCentralQuotient ↥(elementaryGroup Q) κ)) = ⊥ →
      oddCoreIn (fixedSubgroup (autToCentralQuotient (spinGroup Q) α)) = ⊥ :=
    fun κ hκ hN => oddCoreIn_fixed_of_lift_aut hrange (θ := MonoidHom.id (spinGroup Q))
      Function.surjective_id hkerle α α (fun s => rfl) κ hκ hN
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
        rw [MonoidHom.mem_ker, map_mul, map_inv, hα, hcomm_a (spinAction Q x),
          mul_inv_cancel_right, inv_mul_cancel]
      rw [hone]
      have hf : fixedSubgroup (1 : MulAut (spinGroup Q ⧸ Subgroup.center (spinGroup Q))) = ⊤ := by
        ext x
        simp [mem_fixedSubgroup_iff]
      rw [hf]
      have h := CFSG.ClassicalInvolution.Q3.oddCoreIn_range_eq_bot_of_isQuasisimple
        (QuotientGroup.mk' (Subgroup.center (spinGroup Q))) hquasi hZ2
        (by rw [QuotientGroup.ker_mk'])
      rwa [MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h
    · exact hlift' (conjE Q a haO) (fun s => Subtype.ext (hα s).symm)
        (oddCoreIn_fixed_eq_bot_of_involution hF3 hQ (by omega) haO haa hs)
  ·
    have haO : a ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
      rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
      intro v
      rw [hsim, hμ1, one_mul]
    exact hlift' (conjE Q a haO) (fun s => Subtype.ext (hα s).symm)
      (oddCoreIn_fixed_eq_bot_of_cplx hF3 hQ hdim hEq.symm.le haO haa)
  ·
    have hμ' : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
    have hg' : ∀ v, Q (a v) = (-1 : F) * Q v := fun v => by rw [hsim, hμ1]
    exact hlift' (conjES Q hEq hμ' hg') (fun s => Subtype.ext
      ((conjES_apply hEq hμ' hg' _).trans (hα s).symm)) (hIII haa hμ' hg')

end Data

end CFSG.ClassicalInvolution.Q3.Q3MFOD
