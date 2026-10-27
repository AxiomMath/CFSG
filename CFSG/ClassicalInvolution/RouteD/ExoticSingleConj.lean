module

public import CFSG.ClassicalInvolution.RouteD.ExoticSingleSwap
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutMain

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.ModelFacts.OrthAut (SemiSim IsConj eq_of_inv_mul_mem_center)
open scoped Matrix MatrixGroups

section Phi

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem semiSim_phi_eq_id (g : SemiSim Q) (fr : Frame Q)
    (hcomm : ∀ (c : F) z, g (eichler Q fr.e₂ (c • fr.e₁) z) = eichler Q fr.e₂ (c • fr.e₁) (g z))
    (c : F) : g.φ c = c := by
  have hu : Q fr.e₂ = 0 := fr.Q_e₂
  have hw : ∀ c : F, polar Q fr.e₂ (c • fr.e₁) = 0 := fun c => by
    rw [polar_smul_right, fr.polar_e₂_e₁]; simp
  have hQw : ∀ c : F, Q (c • fr.e₁) = 0 := fun c => by
    rw [QuadraticMap.map_smul, fr.Q_e₁, smul_zero]
  have key : ∀ c : F, g.φ c • g fr.e₁ =
      c • (polar Q (g fr.f₂) fr.e₂ • fr.e₁ - polar Q (g fr.f₂) fr.e₁ • fr.e₂) := by
    intro c
    have h1 := hcomm c fr.f₂
    rw [eichler_apply hu (hw c), eichler_apply hu (hw c)] at h1
    simp only [hQw, zero_mul, add_zero, polar_smul_right, fr.polar_f₂_e₂, fr.polar_f₂_e₁,
      mul_zero, zero_smul, sub_zero, smul_eq_mul, mul_one, one_smul] at h1
    rw [g.map_add, g.map_smul] at h1
    rw [sub_eq_add_neg, add_assoc] at h1
    rw [add_left_cancel h1]
    module
  obtain ⟨D, hDdef⟩ : ∃ D : V,
      D = polar Q (g fr.f₂) fr.e₂ • fr.e₁ - polar Q (g fr.f₂) fr.e₁ • fr.e₂ := ⟨_, rfl⟩
  rw [← hDdef] at key
  have hD : g fr.e₁ ≠ 0 := fun h0 => fr.P.e_ne_zero (g.bijective.1 (by rw [h0, g.map_zero']))
  have k1 := key 1
  rw [map_one, one_smul, one_smul] at k1
  have kc := key c
  rw [k1] at kc
  have hc : (g.φ c - c) • D = 0 := by rw [sub_smul, kc, sub_self]
  rcases smul_eq_zero.mp hc with h | h
  · exact sub_eq_zero.mp h
  · exact absurd (k1.trans h) hD

end Phi

section Fixes

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

theorem fixes_of_perfect_of_central {G : Type*} [Group G] {R : Subgroup G} (hR : R ≤ ⁅R, R⁆)
    (α : G ≃* G) (h : ∀ r ∈ R, r⁻¹ * α r ∈ Subgroup.center G) : ∀ r ∈ R, α r = r := by
  have hcomm : ⁅R, R⁆ = R :=
    le_antisymm (Subgroup.commutator_le.mpr fun _ ha _ hb =>
      R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb)) hR
  have hperf : Group.IsPerfect ↥R := Subgroup.isPerfect_iff.mpr hcomm
  have key := eq_of_inv_mul_mem_center ((α : G →* G).comp R.subtype) R.subtype
    (fun x => h x x.2)
  intro r hr
  exact (DFunLike.congr_fun key ⟨r, hr⟩).symm

theorem fixes_twin_of_isConj (hQ : (polarBilin Q).Nondegenerate) (hdim : 5 ≤ Module.finrank F V)
    {α : spinGroup Q ≃* spinGroup Q} {g : SemiSim Q} (hα : IsConj α g) (hα2 : ∀ y, α (α y) = y)
    (hker : (spinAction Q).ker ≤ Subgroup.center (spinGroup Q)) (fr : Frame Q)
    {R R' : Subgroup (spinGroup Q)} (hR' : R' ≤ ⁅R', R'⁆)
    (hR : R.map (spinAction Q) = fr.La.range) (hRs : R'.map (spinAction Q) = fr.swap.La.range)
    (hfix : ∀ r ∈ R, α r = r)
    (hno : ∀ g' : V →ₗ[F] V, Function.Injective g' →
      (∀ x y, polar Q (g' x) y = -polar Q x (g' y)) →
      (∃ c : F, c ≠ 0 ∧ ∀ x, g' (g' x) = c • x) → False) :
    ∀ r ∈ R', α r = r := by
  have hcommR : ∀ (A : SL(2, F)) z, g (fr.La A z) = fr.La A (g z) := by
    intro A z
    have hmem : fr.La A ∈ R.map (spinAction Q) := by rw [hR]; exact ⟨A, rfl⟩
    obtain ⟨r, hr, hrA⟩ := hmem
    have h1 := hα r z
    rw [hfix r hr] at h1
    rw [← hrA]
    exact h1.symm
  have hphi : ∀ c : F, g.φ c = c := by
    refine semiSim_phi_eq_id g fr (fun c z => ?_)
    have := hcommR (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) c) z
    rwa [fr.La_transvection_zero_one c] at this
  let gl : V →ₗ[F] V := g.toLinear hphi
  have hgl : ∀ x, gl x = g x := fun x => rfl
  have hginj : Function.Injective gl := g.bijective.1
  have hμ : ∀ x, Q (gl x) = (g.μ : F) * Q x := fun x => by rw [hgl, g.map_Q, hphi]
  have hG : ∀ ω ∈ elementaryGroup Q, ∀ z, gl (gl (ω z)) = ω (gl (gl z)) := by
    intro ω hω z
    obtain ⟨y, rfl⟩ := elementaryGroup_le_range_spinAction hQ hdim hω
    exact hα.comm_sq hα2 y z
  have hS := commutes_swap_of_commutes_La gl hginj hμ hG fr hcommR hno
  have hact : ∀ r ∈ R', spinAction Q (α r) = spinAction Q r := by
    intro r' hr'
    have hmem : spinAction Q r' ∈ fr.swap.La.range := by rw [← hRs]; exact ⟨r', hr', rfl⟩
    obtain ⟨B, hB⟩ := hmem
    refine LinearEquiv.ext fun w => ?_
    obtain ⟨z, rfl⟩ := g.bijective.2 w
    calc spinAction Q (α r') (g z) = g (spinAction Q r' z) := hα r' z
      _ = g (fr.swap.La B z) := by rw [← hB]
      _ = fr.swap.La B (g z) := hS B z
      _ = spinAction Q r' (g z) := by rw [hB]
  exact fixes_of_perfect_of_central hR' α fun r hr =>
    hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hact r hr, inv_mul_cancel])

end Fixes

end CFSG.ClassicalInvolution.RouteD.Exotic
