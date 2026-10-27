module

public import CFSG.ClassicalGroups.Unitary.Action

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank

section Center

variable {K : Type} [Field K] {σ : K ≃+* K} {m : ℕ}

theorem center_SUid_eq (hσ : IsUnitaryInvolution σ) (hm : 3 ≤ m) :
    Subgroup.center (SUid σ m) = (StatedScalars (Fin m) K).subgroupOf (SUid σ m) := by
  apply le_antisymm
  · intro z hz
    refine mem_scalars_of_smul_eq hσ hm fun x => ?_
    induction x using isoPts_ind with
    | h v hv0 hv =>
    rw [smul_pt]
    obtain ⟨τ, hτ0, hτ⟩ := hσ.exists_traceZero
    let t : SUid σ m := tv hσ.invol hv hτ
    have hct : z * t * z⁻¹ = t := by
      rw [(Subgroup.mem_center_iff.1 hz t).symm, mul_inv_cancel_right]
    obtain ⟨y, hy⟩ := exists_herm_ne_zero σ hv0
    have hact : (τ * herm σ (z • v) y) • (z • v) = (τ * herm σ v y) • v := by
      have h1 := conj_smul_of_tv z t (tv_smul hσ.invol hv hτ) y
      rw [hct, tv_smul hσ.invol hv hτ] at h1
      exact (add_left_cancel h1).symm
    have hzv : herm σ (z • v) y ≠ 0 := by
      intro h0
      rw [h0, mul_zero, zero_smul] at hact
      exact hv0 ((smul_eq_zero.mp hact.symm).resolve_left (mul_ne_zero hτ0 hy))
    refine (pt_eq_pt_iff _ _ _ _).mpr ⟨(τ * herm σ (z • v) y)⁻¹ * (τ * herm σ v y), ?_⟩
    rw [mul_smul, ← hact, smul_smul, inv_mul_cancel₀ (mul_ne_zero hτ0 hzv), one_smul]
  · intro g hg
    rw [Subgroup.mem_subgroupOf, StatedScalars,
      ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hg
    exact Subgroup.mem_center_iff.2 fun h => Subtype.ext (Subgroup.mem_center_iff.1 hg h)

end Center

end CFSG.ClassicalInvolution.Phan
