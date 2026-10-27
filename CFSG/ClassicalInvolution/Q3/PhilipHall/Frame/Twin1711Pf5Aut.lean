module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711PfCover

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711

theorem autInner_cover {E Q : Type} [Group E] [Group Q] (q : E →* Q) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center E) (hperf : Group.IsPerfect E)
    (hQc : Subgroup.center Q = ⊥) (hQ : ∀ γ : MulAut Q, ∃ g : Q, γ = MulAut.conj g) :
    ∀ α : MulAut E, ∃ g : E, α = MulAut.conj g := by
  intro α
  have hcen : Subgroup.center E = q.ker := center_eq_ker_of_centerless q hq hker hQc
  have hαc : ∀ x ∈ Subgroup.center E, α x ∈ Subgroup.center E := by
    intro x hx
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro y
    obtain ⟨y', rfl⟩ := α.surjective y
    rw [← map_mul, ← map_mul, hx y']
  have hmap : q.ker.map (α : E →* E) = q.ker := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [← hcen] at hx ⊢
      exact hαc x hx
    · intro y hy
      refine ⟨α.symm y, ?_, by simp⟩
      have hy' : y ∈ Subgroup.center E := by rw [hcen]; exact hy
      have hs : α.symm y ∈ Subgroup.center E := by
        rw [Subgroup.mem_center_iff] at hy' ⊢
        intro z
        obtain ⟨z', rfl⟩ := α.symm.surjective z
        rw [← map_mul, ← map_mul, hy' z']
      rw [hcen] at hs
      exact hs
  let e : E ⧸ q.ker ≃* Q := QuotientGroup.quotientKerEquivOfSurjective q hq
  let f : E ⧸ q.ker ≃* E ⧸ q.ker := QuotientGroup.congr q.ker q.ker α hmap
  let γ : MulAut Q := e.symm.trans (f.trans e)
  have hγ : ∀ y : E, γ (q y) = q (α y) := by
    intro y
    have h1 : e.symm (q y) = (y : E ⧸ q.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show e (f (e.symm (q y))) = q (α y)
    rw [h1]
    rfl
  obtain ⟨gb, hgb⟩ := hQ γ
  obtain ⟨g, rfl⟩ := hq gb
  let σ : MulAut E := α.trans (MulAut.conj g⁻¹)
  have hσ : ∀ x : E, σ x * ((1 : MulAut E) x)⁻¹ ∈ Subgroup.center E := by
    intro x
    rw [hcen, MonoidHom.mem_ker]
    show q (g⁻¹ * α x * g⁻¹⁻¹ * x⁻¹) = 1
    have h1 := hγ x
    rw [hgb] at h1
    simp only [MulAut.conj_apply] at h1
    simp only [map_mul, map_inv, ← h1]
    group
  have hσ1 := GorensteinWalter.perfect_central_automorphism_eq hperf σ 1 hσ
  refine ⟨g, MulEquiv.ext fun x => ?_⟩
  have := congrArg (fun τ : MulAut E => τ x) hσ1
  simp only [σ, MulEquiv.trans_apply, MulAut.conj_apply, MulAut.one_apply] at this
  rw [MulAut.conj_apply]
  calc α x = g * (g⁻¹ * α x * g⁻¹⁻¹) * g⁻¹ := by group
    _ = g * x * g⁻¹ := by rw [this]

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711
