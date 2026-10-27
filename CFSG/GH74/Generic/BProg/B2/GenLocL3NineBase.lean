module

public import CFSG.GH74.Generic.BProg.B2.GenLocL3NineSL2
public import CFSG.GH74.Generic.BProg.B2.GenLocL3Seven
public import CFSG.GH74.Generic.BProg.B2.GenLocL3Pair

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup CFSG.Blueprint CFSG.GorensteinWalter CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.AutL2Facts CFSG.ComponentClassification.CatalogueBHigherLinearAction Matrix
  GenLocL3Good GenLocL3Pair GenLocL3Seven
open scoped MatrixGroups

namespace GenLocL3Nine

variable {K : Type} [Field K]

theorem exists_data {y : MulAut (LinearFlag.projectiveSL 3 K)} (hy : y ∈ frameStab 3 K) :
    ∃ (u : Fin 3 → Kˣ) (σ : K ≃+* K) (ε : ℕ), ε ≤ 1 ∧
      y = LinearFlag.conjAut 3 K (diag3 u) * LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K ^ ε := by
  obtain ⟨x, σ, ε, hx, hε, rfl⟩ := GenLocL3NFFrame.mem_frameStab_iff.1 hy
  obtain ⟨u, rfl⟩ := exists_diag3 hx
  exact ⟨u, σ, ε, hε, rfl⟩

theorem restM_dual_fieldAut_comm [Finite K] (σ : K ≃+* K) (m : Fin 3) :
    slConjugation 2 K Jgl * GLS.IVK.Lifted.slFieldAut σ =
      GLS.IVK.Lifted.slFieldAut σ * slConjugation 2 K Jgl := by
  have h : (⟨LinearFlag.dualAut 3 K, GenLocL3NFAux.dualAut_mem_frameStab⟩ : frameStab 3 K) *
      ⟨LinearFlag.fieldAut 3 K σ, GenLocL3NFAux.fieldAut_mem_frameStab σ⟩ =
      ⟨LinearFlag.fieldAut 3 K σ, GenLocL3NFAux.fieldAut_mem_frameStab σ⟩ *
        ⟨LinearFlag.dualAut 3 K, GenLocL3NFAux.dualAut_mem_frameStab⟩ :=
    Subtype.ext (LinearFlag.dualAut_mul_fieldAut σ)
  have := congrArg (restM m) h
  rw [map_mul, map_mul, restM_dualAut, restM_fieldAut] at this
  exact this

theorem rho_data [Finite K] (m : Fin 3) {y : MulAut (LinearFlag.projectiveSL 3 K)}
    (hy : y ∈ frameStab 3 K) {u : Fin 3 → Kˣ} {σ : K ≃+* K} {ε : ℕ} (hε : ε ≤ 1)
    (h : y = LinearFlag.conjAut 3 K (diag3 u) * LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K ^ ε) :
    restM m ⟨y, hy⟩ = slConjugation 2 K (diag2 (u (crd m 0)) (u (crd m 1)) * Jgl ^ ε) *
      GLS.IVK.Lifted.slFieldAut σ := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · have : (⟨y, hy⟩ : frameStab 3 K) =
        ⟨LinearFlag.conjAut 3 K (diag3 u), GenLocL3NFAux.conjAut_mem_frameStab (isDiag_diag3 u)⟩ *
          ⟨LinearFlag.fieldAut 3 K σ, GenLocL3NFAux.fieldAut_mem_frameStab σ⟩ :=
      Subtype.ext (by
        show y = LinearFlag.conjAut 3 K (diag3 u) * LinearFlag.fieldAut 3 K σ
        rw [h, pow_zero, mul_one])
    rw [this, map_mul, restM_conjAut, restM_fieldAut, pow_zero, mul_one]
  · have : (⟨y, hy⟩ : frameStab 3 K) =
        ⟨LinearFlag.conjAut 3 K (diag3 u), GenLocL3NFAux.conjAut_mem_frameStab (isDiag_diag3 u)⟩ *
          ⟨LinearFlag.fieldAut 3 K σ, GenLocL3NFAux.fieldAut_mem_frameStab σ⟩ *
          ⟨LinearFlag.dualAut 3 K, GenLocL3NFAux.dualAut_mem_frameStab⟩ :=
      Subtype.ext (by
        show y = LinearFlag.conjAut 3 K (diag3 u) * LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K
        rw [h, pow_one])
    rw [this, map_mul, map_mul, restM_conjAut, restM_fieldAut, restM_dualAut, pow_one, map_mul, mul_assoc,
      mul_assoc, restM_dual_fieldAut_comm σ m]


theorem rho_eq_one_of_eq [Finite K] (m : Fin 3) {y : MulAut (LinearFlag.projectiveSL 3 K)}
    (hy : y ∈ frameStab 3 K) {u : Fin 3 → Kˣ} (h : y = LinearFlag.conjAut 3 K (diag3 u))
    (hu : u (crd m 0) = u (crd m 1)) : restM m ⟨y, hy⟩ = 1 := by
  have h' : y = LinearFlag.conjAut 3 K (diag3 u) * LinearFlag.fieldAut 3 K 1 *
      LinearFlag.dualAut 3 K ^ 0 := by rw [h, map_one, pow_zero, mul_one, mul_one]
  rw [rho_data m hy (Nat.zero_le 1) h', hu, pow_zero, mul_one, slConjugation_diag2_self]
  have : GLS.IVK.Lifted.slFieldAut (1 : K ≃+* K) = 1 := by
    refine MulEquiv.ext fun g => ?_
    rw [GLS.IVK.Lifted.slFieldAut_apply]
    ext i j
    simp
  rw [this, one_mul]

theorem rho_not_inner_of_field [Finite K] (m : Fin 3) {y : MulAut (LinearFlag.projectiveSL 3 K)}
    (hy : y ∈ frameStab 3 K) {u : Fin 3 → Kˣ} {σ : K ≃+* K} {ε : ℕ} (hε : ε ≤ 1)
    (h : y = LinearFlag.conjAut 3 K (diag3 u) * LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K ^ ε)
    (hσ : σ ≠ 1) : restM m ⟨y, hy⟩ ∉ (MulAut.conj : SL(2, K) →* MulAut SL(2, K)).range := by
  rw [rho_data m hy hε h]
  exact slConj_mul_slFieldAut_not_inner _ hσ

theorem det_diag2_mul_J_pow {K : Type} [Field K] (a b : Kˣ) (ε : ℕ) :
    (((diag2 a b : GL (Fin 2) K) * Jgl ^ ε : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det =
      (a : K) * b := by
  rw [Units.val_mul, Matrix.det_mul, det_diag2, Units.val_pow_eq_pow_val, Matrix.det_pow]
  have : ((Jgl : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    simp [coe_Jgl, Matrix.det_fin_two]
  rw [this, one_pow, mul_one]

theorem isSquare_of_rho_inner [Finite K] (m : Fin 3) {y : MulAut (LinearFlag.projectiveSL 3 K)}
    (hy : y ∈ frameStab 3 K) {u : Fin 3 → Kˣ} {ε : ℕ} (hε : ε ≤ 1)
    (h : y = LinearFlag.conjAut 3 K (diag3 u) * LinearFlag.fieldAut 3 K 1 * LinearFlag.dualAut 3 K ^ ε)
    (hin : restM m ⟨y, hy⟩ ∈ (MulAut.conj : SL(2, K) →* MulAut SL(2, K)).range) :
    IsSquare ((u (crd m 0) : K) * u (crd m 1)) := by
  have h1 := rho_data m hy hε h
  have h2 : GLS.IVK.Lifted.slFieldAut (1 : K ≃+* K) = 1 := by
    refine MulEquiv.ext fun g => ?_
    rw [GLS.IVK.Lifted.slFieldAut_apply]
    ext i j
    simp
  rw [h1, h2, mul_one] at hin
  have := isSquare_det_of_mem_inn _ hin
  rwa [det_diag2_mul_J_pow] at this


theorem conjAut_diag3_smul (lam : Kˣ) (u : Fin 3 → Kˣ) :
    LinearFlag.conjAut 3 K (diag3 (fun i => lam * u i)) = LinearFlag.conjAut 3 K (diag3 u) := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective 3 K x
  rw [LinearFlag.conjAut_proj, LinearFlag.conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [LinearFlag.coe_slConjugation, LinearFlag.coe_slConjugation, coe_diag3, coe_diag3_inv, coe_diag3,
    coe_diag3_inv]
  ext i j
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Units.val_mul, _root_.mul_inv_rev, Units.val_inv_eq_inv_val]
  simp [Finset.sum_ite_eq]
  field_simp

theorem exists_block_eq {u : Fin 3 → Kˣ} (h : ∀ i j, ((u i : K) * u i) = (u j : K) * u j) :
    ∃ m : Fin 3, u (crd m 0) = u (crd m 1) := by
  have h1 : u 1 = u 0 ∨ (u 1 : K) = -(u 0 : K) := by
    have : ((u 1 : K) - u 0) * ((u 1 : K) + u 0) = 0 := by linear_combination h 1 0
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (Units.ext (by linear_combination h))
    · exact Or.inr (by linear_combination h)
  have h2 : u 2 = u 0 ∨ (u 2 : K) = -(u 0 : K) := by
    have : ((u 2 : K) - u 0) * ((u 2 : K) + u 0) = 0 := by linear_combination h 2 0
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (Units.ext (by linear_combination h))
    · exact Or.inr (by linear_combination h)
  rcases h1 with h1 | h1
  · exact ⟨2, h1.symm⟩
  · rcases h2 with h2 | h2
    · exact ⟨1, h2.symm⟩
    · exact ⟨0, Units.ext (by show (u 1 : K) = u 2; rw [h1, h2])⟩


theorem slConj_diag2_J_anti (a b : Kˣ) {β : K} (hβ : β ≠ 0) (hrel : β * β * (b : K) = (a : K)) :
    slConjugation 2 K (diag2 a b * Jgl) (anti hβ) = anti hβ := by
  apply Subtype.ext
  rw [LinearFlag.coe_slConjugation, Units.val_mul, _root_.mul_inv_rev, Units.val_mul, coe_diag2,
    coe_Jgl, coe_Jgl_inv, coe_diag2_inv]
  have hb : (b : K) ≠ 0 := b.ne_zero
  have ha : (a : K) ≠ 0 := a.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [anti, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, Units.val_inv_eq_inv_val,
      Matrix.vecMul_diagonal]
  · field_simp
    linear_combination (-1 : K) * hrel
  · field_simp
    linear_combination hrel


theorem slFieldAut_one [Finite K] : GLS.IVK.Lifted.slFieldAut (1 : K ≃+* K) = 1 := by
  refine MulEquiv.ext fun g => ?_
  rw [GLS.IVK.Lifted.slFieldAut_apply]
  ext i j
  simp

theorem fixed_anti_of_reflection [Finite K] (m : Fin 3) {y : MulAut (LinearFlag.projectiveSL 3 K)}
    (hy : y ∈ frameStab 3 K) {u : Fin 3 → Kˣ}
    (h : y = LinearFlag.conjAut 3 K (diag3 u) * LinearFlag.fieldAut 3 K 1 * LinearFlag.dualAut 3 K ^ 1)
    {β : K} (hβ : β ≠ 0) (hrel : β * β * (u (crd m 1) : K) = (u (crd m 0) : K)) :
    y (phiM m (anti hβ)) = phiM m (anti hβ) := by
  have h1 := restM_spec m ⟨y, hy⟩ (anti hβ)
  rw [rho_data m hy le_rfl h, pow_one, slFieldAut_one, mul_one] at h1
  rw [show (⟨y, hy⟩ : frameStab 3 K).1 = y from rfl] at h1
  rw [h1, slConj_diag2_J_anti _ _ hβ hrel]

theorem eq_of_scalar_aux (u u' : Fin 3 → Kˣ) (j k r : Fin 3) (hcov : ∀ i, i = j ∨ i = k ∨ i = r)
    (hsq : ∀ i i', (u i : K) * u i = u i' * u i') (hsq' : ∀ i i', (u' i : K) * u' i = u' i' * u' i')
    (hjk : u j = u k) (hjk' : u' j = u' k)
    (hne : LinearFlag.conjAut 3 K (diag3 u) ≠ 1) (hne' : LinearFlag.conjAut 3 K (diag3 u') ≠ 1) :
    LinearFlag.conjAut 3 K (diag3 u) = LinearFlag.conjAut 3 K (diag3 u') := by
  have hsc : ∀ (w : Fin 3 → Kˣ) (c : Kˣ), (∀ i, w i = c) → LinearFlag.conjAut 3 K (diag3 w) = 1 := by
    intro w c hw
    have : w = fun i => c * (fun _ => (1 : Kˣ)) i := by
      funext i; simp [hw i]
    rw [this, conjAut_diag3_smul]
    have h1 : diag3 (fun _ : Fin 3 => (1 : Kˣ)) = (1 : GL (Fin 3) K) := by
      apply Units.ext
      rw [coe_diag3]
      simp
    rw [h1, map_one]
  have key : ∀ (w : Fin 3 → Kˣ), (∀ i i', (w i : K) * w i = w i' * w i') → w j = w k →
      LinearFlag.conjAut 3 K (diag3 w) ≠ 1 → (w r : K) = -(w j : K) := by
    intro w hw hjkw hnew
    have : ((w r : K) - w j) * ((w r : K) + w j) = 0 := by linear_combination hw r j
    rcases mul_eq_zero.1 this with h | h
    · exfalso
      apply hnew
      refine hsc w (w j) fun i => ?_
      rcases hcov i with rfl | rfl | rfl
      · rfl
      · exact hjkw.symm
      · exact Units.ext (by linear_combination h)
    · linear_combination h
  have e1 := key u hsq hjk hne
  have e2 := key u' hsq' hjk' hne'
  have hu0 : (u j : K) ≠ 0 := (u j).ne_zero
  have : u' = fun i => (u' j * (u j)⁻¹) * u i := by
    funext i
    rcases hcov i with rfl | rfl | rfl
    · simp
    · rw [← hjk, ← hjk']; simp
    · apply Units.ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      rw [e1, e2]
      field_simp
  rw [this, conjAut_diag3_smul]


theorem eq_of_trivial_block (m : Fin 3) {u u' : Fin 3 → Kˣ}
    (hsq : ∀ i i', (u i : K) * u i = u i' * u i') (hsq' : ∀ i i', (u' i : K) * u' i = u' i' * u' i')
    (hm : u (crd m 0) = u (crd m 1)) (hm' : u' (crd m 0) = u' (crd m 1))
    (hne : LinearFlag.conjAut 3 K (diag3 u) ≠ 1) (hne' : LinearFlag.conjAut 3 K (diag3 u') ≠ 1) :
    LinearFlag.conjAut 3 K (diag3 u) = LinearFlag.conjAut 3 K (diag3 u') := by
  fin_cases m
  · exact eq_of_scalar_aux u u' 1 2 0 (by decide) hsq hsq' hm hm' hne hne'
  · exact eq_of_scalar_aux u u' 0 2 1 (by decide) hsq hsq' hm hm' hne hne'
  · exact eq_of_scalar_aux u u' 0 1 2 (by decide) hsq hsq' hm hm' hne hne'

theorem sq_equal_of_conjAut_sq [Finite K] (u : Fin 3 → Kˣ)
    (h : LinearFlag.conjAut 3 K (diag3 u) * LinearFlag.conjAut 3 K (diag3 u) = 1) :
    ∀ i i', ((u i : Kˣ) : K) * u i = (u i' : K) * u i' := by
  obtain ⟨c, hc0, hc⟩ := GenLocL3NFAux.scalar_of_conjAut_eq (diag3 u * diag3 u) 1
    (by rw [map_mul, map_one, h])
  have hd : ∀ j, c * ((u j : K) * (u j : K)) = 1 := by
    intro j
    have := congrFun (congrFun hc j) j
    simp only [Units.val_one, Matrix.one_apply_eq, Units.val_mul, coe_diag3, Matrix.diagonal_mul_diagonal,
      Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul] at this
    linear_combination -this
  intro i i'
  have : c * ((u i : K) * (u i : K)) = c * ((u i' : K) * (u i' : K)) := by rw [hd i, hd i']
  exact mul_left_cancel₀ hc0 this


end GenLocL3Nine

end CFSG.GH74.Generic.BProg.B2
