module

public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Anisotropic.Embed
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Anisotropic.Generation

public section

namespace CFSG.ClassicalInvolution.Models.OrthogonalPairs

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg CFSG.ClassicalInvolution.Models
open scoped MatrixGroups

variable {K K' V : Type} [Field K] [Field K'] [Algebra K K'] {σ : K' ≃+* K'} [AddCommGroup V]
  [Module K V] {Q : QuadraticForm K V}

namespace QuadExt

variable (E : QuadExt K K' σ)

theorem flipAt_flipAt (j : Fin 3) (x : Fin 3 → K') : E.flipAt j (E.flipAt j x) = x := by
  funext i
  rw [E.flipAt_apply, E.flipAt_apply]
  by_cases h : i = j
  · simp [h, E.isUnitary.invol]
  · simp [h]

theorem flipAt_symm (j : Fin 3) : (E.flipAt j).symm = E.flipAt j := by
  refine LinearEquiv.ext fun x => ?_
  rw [LinearEquiv.symm_apply_eq, E.flipAt_flipAt]

theorem flipAt_apply_self (j : Fin 3) (x : Fin 3 → K') : E.flipAt j x j = σ (x j) := by
  rw [E.flipAt_apply]
  simp

theorem flipAt_embSUid_smul (c : Fin 3) (A : SUid σ 2) (x : Fin 3 → K') :
    E.flipAt c (embSUid σ c A • x) = embSUid σ c A • E.flipAt c x := by
  rw [smul_def, coe_embSUid, smul_def, coe_embSUid]
  fin_cases c <;> ext i <;> fin_cases i <;>
    simp [E.flipAt_apply, embPair, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem flipAt_single_one_smul {c' : Fin 3} (hc' : c' ≠ 1) (l : K') :
    E.flipAt c' (l • (Pi.single 1 1 : Fin 3 → K')) = l • Pi.single 1 1 := by
  funext i
  rw [E.flipAt_apply]
  by_cases h : i = c'
  · subst h
    simp [hc']
  · simp [h]

theorem not_flip_conj_eq_rho (hne : ∃ c : K', σ c ≠ c) {c' : Fin 3} (hc' : c' ≠ 1)
    {g : SUid σ 3} (hg : (g • (Pi.single 1 1 : Fin 3 → K')) c' ≠ 0) (h : SUid σ 3) :
    (E.flipAt c').toLinearMap ∘ₗ suEnd g ∘ₗ (E.flipAt c').toLinearMap ≠ suEnd (K := K) h := by
  intro hEq
  set γ := (g • (Pi.single 1 1 : Fin 3 → K')) c' with hγ
  have key : ∀ l : K', σ l * σ γ = l * σ γ := by
    intro l
    have h1 := congrArg (fun v => v c') (LinearMap.congr_fun hEq (l • Pi.single 1 1))
    have h0 := congrArg (fun v => v c') (LinearMap.congr_fun hEq (Pi.single 1 1))
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, suEnd_apply] at h1 h0
    rw [E.flipAt_single_one_smul hc', smul_comm, E.flipAt_apply_self, smul_comm h] at h1
    have h0' : σ γ = (h • (Pi.single 1 1 : Fin 3 → K')) c' := by
      have := h0
      rw [← one_smul K' (Pi.single 1 1 : Fin 3 → K'), E.flipAt_single_one_smul hc',
        E.flipAt_apply_self] at this
      simpa using this
    simp only [Pi.smul_apply, smul_eq_mul, map_mul] at h1
    rw [← h0']  at h1
    exact h1
  obtain ⟨c, hc⟩ := hne
  have hσγ : σ γ ≠ 0 := (map_ne_zero σ).mpr hg
  exact hc (mul_right_cancel₀ hσγ (key c))


end QuadExt

namespace UnitaryEmbedding

variable (D : UnitaryEmbedding Q σ) (E : QuadExt K K' σ)

theorem embLin_injective {S S' : Module.End K (Fin 3 → K')} (h : D.embLin S = D.embLin S') :
    S = S' := by
  refine LinearMap.ext fun z => ?_
  have := congrArg (fun T : V →ₗ[K] V => D.coords (T (D.incl z))) h
  simpa [embLin_apply, D.coords_incl] using this

@[expose] def flip (j : Fin 3) : UnitaryEmbedding Q σ :=
  D.twist (E.flipAt j) (E.herm_flipAt j)

theorem flip_embLin (j : Fin 3) (S : Module.End K (Fin 3 → K')) :
    (D.flip E j).embLin S =
      D.embLin ((E.flipAt j).toLinearMap ∘ₗ S ∘ₗ (E.flipAt j).toLinearMap) := by
  rw [flip, D.twist_embLin, E.flipAt_symm]

theorem flip_theta_apply (j : Fin 3) (g : SUid σ 3) (x : V) :
    (D.flip E j).theta g x =
      D.embLin ((E.flipAt j).toLinearMap ∘ₗ suEnd g ∘ₗ (E.flipAt j).toLinearMap) x := by
  rw [← flip_embLin]
  exact (D.flip E j).embHom_apply suEnd g x


theorem flip_theta_of_mem_range (c : Fin 3) {g : SUid σ 3} (hg : g ∈ (embSUid σ c).range) :
    (D.flip E c).theta g = D.theta g := by
  obtain ⟨A, rfl⟩ := hg
  refine LinearEquiv.ext fun x => ?_
  rw [flip_theta_apply]
  have : (E.flipAt c).toLinearMap ∘ₗ suEnd (embSUid σ c A) ∘ₗ (E.flipAt c).toLinearMap =
      suEnd (embSUid σ c A) := by
    refine LinearMap.ext fun y => ?_
    simp [suEnd_apply, E.flipAt_embSUid_smul, E.flipAt_flipAt]
  rw [this]
  exact (D.embHom_apply suEnd _ x).symm

theorem flip_theta_not_mem_range (hne : ∃ c : K', σ c ≠ c) {c' : Fin 3} (hc' : c' ≠ 1)
    {g : SUid σ 3} (hg : (g • (Pi.single 1 1 : Fin 3 → K')) c' ≠ 0) :
    (D.flip E c').theta g ∉ D.theta.range := by
  rintro ⟨h, hh⟩
  refine E.not_flip_conj_eq_rho hne hc' hg h ?_
  refine D.embLin_injective (LinearMap.ext fun x => ?_)
  rw [← flip_theta_apply, ← hh]
  exact (D.embHom_apply suEnd h x).symm


theorem flip_map_ne (hne : ∃ c : K', σ c ≠ c) {c c' : Fin 3} (hc' : c' ≠ 1) {g : SUid σ 3}
    (hgc : g ∈ (embSUid σ c).range) (hg : (g • (Pi.single 1 1 : Fin 3 → K')) c' ≠ 0) :
    (embSUid σ c).range.map (D.flip E c').theta ≠ (embSUid σ c).range.map D.theta := by
  intro h
  have hmem : (D.flip E c').theta g ∈ (embSUid σ c).range.map (D.flip E c').theta := ⟨g, hgc, rfl⟩
  rw [h] at hmem
  exact D.flip_theta_not_mem_range E hne hc' hg (Subgroup.map_le_range _ _ hmem)

end UnitaryEmbedding

theorem exists_block_two (hσ : IsUnitaryInvolution σ) (W : WittData σ) {x : K'}
    (hx : x + σ x = 0) (hx0 : x ≠ 0) :
    ∃ g ∈ (embSUid σ 2).range, (g • (Pi.single 1 1 : Fin 3 → K')) 0 ≠ 0 := by
  have ha : herm σ (W.hypA 0) (W.hypA 0) = 0 := W.herm_hypA_hypA
  refine ⟨embSUid σ 2 (tv hσ.invol ha hx), ⟨_, rfl⟩, ?_⟩
  rw [embSUid_tv, tv_smul]
  simp [herm_single_right, insZero]
  exact ⟨hx0, W.u_ne_zero⟩

theorem exists_block_zero (hσ : IsUnitaryInvolution σ) (W : WittData σ) {x : K'}
    (hx : x + σ x = 0) (hx0 : x ≠ 0) :
    ∃ g ∈ (embSUid σ 0).range, (g • (Pi.single 1 1 : Fin 3 → K')) 2 ≠ 0 := by
  have ha : herm σ (W.hypA 0) (W.hypA 0) = 0 := W.herm_hypA_hypA
  refine ⟨embSUid σ 0 (tv hσ.invol ha hx), ⟨_, rfl⟩, ?_⟩
  rw [embSUid_tv, tv_smul]
  simp [herm_single_right, insZero]
  exact ⟨hx0, W.u_ne_zero⟩

end CFSG.ClassicalInvolution.Models.OrthogonalPairs
