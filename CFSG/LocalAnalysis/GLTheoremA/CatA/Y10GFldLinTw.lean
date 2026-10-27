module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinFldGrp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GFldLinTw

open CFSG.Open CFSG.Assembly CFSG.LieType.SemisimpleCentralizers.HeldLang
open CFSG.HardMathSupport.Foote.ModuleExclusions
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.Y10GInnLinFld (mk_eq_scalar exists_scalar_of_conj_mod_scalar)

variable {K : Type} [Field K]

section Transvection

variable {d : ℕ}

def fin0 (hd : 2 ≤ d) : Fin d := ⟨0, by omega⟩

def fin1 (hd : 2 ≤ d) : Fin d := ⟨1, by omega⟩

theorem fin0_ne_fin1 (hd : 2 ≤ d) : fin0 hd ≠ fin1 hd := by
  intro h
  have := congrArg Fin.val h
  simp [fin0, fin1] at this

noncomputable def tvGL (hd : 2 ≤ d) (b : K) : GL (Fin d) K :=
  Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection (fin0_ne_fin1 hd) b)

theorem tvGL_mem (hd : 2 ≤ d) (b : K) : tvGL hd b ∈ slGL (Fin d) K := by
  rw [mem_slGL]
  exact (Matrix.SpecialLinearGroup.transvection (fin0_ne_fin1 hd) b).2

theorem tvGL_coe (hd : 2 ≤ d) (b : K) :
    ((tvGL hd b : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (1 : Matrix (Fin d) (Fin d) K) + Matrix.single (fin0 hd) (fin1 hd) b := by
  rw [tvGL, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.transvection_coe]

theorem glMap_tvGL (hd : 2 ≤ d) (τ : K ≃+* K) (b : K) : glMap τ (tvGL hd b) = tvGL hd (τ b) := by
  apply Units.ext
  rw [coe_glMap, tvGL_coe, tvGL_coe]
  ext i j
  by_cases h : i = fin0 hd ∧ j = fin1 hd
  · obtain ⟨rfl, rfl⟩ := h
    simp [Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  · have hi : ¬ (i = fin0 hd ∧ j = fin1 hd) := h
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, hi, if_false,
      add_zero, map_zero]
    split_ifs <;> simp


theorem scalar_eq_smul_one (a : K) :
    Matrix.scalar (Fin d) a = a • (1 : Matrix (Fin d) (Fin d) K) := by
  rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem entry_mul_one_add_single (M : Matrix (Fin d) (Fin d) K) (e0 e1 : Fin d) (t : K) (i j : Fin d) :
    (M * ((1 : Matrix (Fin d) (Fin d) K) + Matrix.single e0 e1 t)) i j =
      M i j + (if j = e1 then M i e0 * t else 0) := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  by_cases hj : j = e1
  · subst hj
    simp [Matrix.mul_single_apply_same]
  · simp [Matrix.mul_single_apply_of_ne, hj]

theorem entry_one_add_single_mul (M : Matrix (Fin d) (Fin d) K) (e0 e1 : Fin d) (t : K) (i j : Fin d) :
    ((1 + Matrix.single e0 e1 t : Matrix (Fin d) (Fin d) K) * M) i j =
      M i j + (if i = e0 then t * M e1 j else 0) := by
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply]
  by_cases hi : i = e0
  · subst hi
    simp [Matrix.single_mul_apply_same]
  · simp [Matrix.single_mul_apply_of_ne, hi]

theorem mu_eq_one_of_three_le {d : ℕ} (hd : 3 ≤ d) (N : GL (Fin d) K) (s b : K) (μ : Kˣ)
    (h : N * tvGL (show 2 ≤ d by omega) s * N⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin d) μ * tvGL (show 2 ≤ d by omega) b) :
    μ = 1 := by
  have hd2 : 2 ≤ d := by omega
  by_contra hμ
  have hμ' : (μ : K) ≠ 1 := fun h1 => hμ (Units.ext h1)
  have hE : (N : Matrix (Fin d) (Fin d) K) *
      ((1 : Matrix (Fin d) (Fin d) K) + Matrix.single (fin0 hd2) (fin1 hd2) s) =
      (μ : K) • (((1 : Matrix (Fin d) (Fin d) K) + Matrix.single (fin0 hd2) (fin1 hd2) b) *
        (N : Matrix (Fin d) (Fin d) K)) := by
    have h' : N * tvGL hd2 s = Matrix.GeneralLinearGroup.scalar (Fin d) μ * tvGL hd2 b * N := by
      rw [← h]
      group
    have h'' := congrArg (fun g : GL (Fin d) K => (g : Matrix (Fin d) (Fin d) K)) h'
    simp only [Units.val_mul, tvGL_coe, Matrix.GeneralLinearGroup.coe_scalar, scalar_eq_smul_one,
      smul_mul_assoc, one_mul] at h''
    exact h''
  have hent : ∀ i j : Fin d,
      (N : Matrix (Fin d) (Fin d) K) i j +
          (if j = fin1 hd2 then (N : Matrix (Fin d) (Fin d) K) i (fin0 hd2) * s else 0) =
        (μ : K) * ((N : Matrix (Fin d) (Fin d) K) i j +
          (if i = fin0 hd2 then b * (N : Matrix (Fin d) (Fin d) K) (fin1 hd2) j else 0)) := by
    intro i j
    have := congrFun (congrFun hE i) j
    rw [entry_mul_one_add_single, Matrix.smul_apply, smul_eq_mul, entry_one_add_single_mul] at this
    exact this
  have hzero : ∀ i j : Fin d, i ≠ fin0 hd2 → j ≠ fin1 hd2 → (N : Matrix (Fin d) (Fin d) K) i j = 0 := by
    intro i j hi hj
    have h1 := hent i j
    simp only [if_neg hj, if_neg hi, add_zero] at h1
    have h2 : (1 - (μ : K)) * (N : Matrix (Fin d) (Fin d) K) i j = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd (sub_eq_zero.1 h3).symm hμ'
    · exact h3
  set M : Matrix (Fin d) (Fin d) K := (N : Matrix (Fin d) (Fin d) K) with hM
  obtain ⟨M', hM'⟩ : ∃ M' : Matrix (Fin d) (Fin d) K, M' = ((N⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
    ⟨_, rfl⟩
  have hM'M : M' * M = 1 := by
    rw [hM', hM, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  set e2 : Fin d := ⟨2, by omega⟩ with he2
  have e0e2 : fin0 hd2 ≠ e2 := by
    intro h
    have := congrArg Fin.val h
    simp [fin0, he2] at this
  have e1e2 : fin1 hd2 ≠ e2 := by
    intro h
    have := congrArg Fin.val h
    simp [fin1, he2] at this
  have hcol0 : ∀ k, k ≠ fin0 hd2 → M k (fin0 hd2) = 0 := fun k hk => hzero k _ hk (fin0_ne_fin1 hd2)
  have hcol2 : ∀ k, k ≠ fin0 hd2 → M k e2 = 0 := fun k hk => hzero k _ hk e1e2.symm
  have h1 : M' (fin0 hd2) (fin0 hd2) * M (fin0 hd2) (fin0 hd2) = 1 := by
    have := congrFun (congrFun hM'M (fin0 hd2)) (fin0 hd2)
    rw [Matrix.mul_apply, Finset.sum_eq_single (fin0 hd2) (fun k _ hk => by rw [hcol0 k hk, mul_zero])
      (fun h => absurd (Finset.mem_univ _) h), Matrix.one_apply_eq] at this
    exact this
  have h2 : M' (fin0 hd2) (fin0 hd2) * M (fin0 hd2) e2 = 0 := by
    have := congrFun (congrFun hM'M (fin0 hd2)) e2
    rw [Matrix.mul_apply, Finset.sum_eq_single (fin0 hd2) (fun k _ hk => by rw [hcol2 k hk, mul_zero])
      (fun h => absurd (Finset.mem_univ _) h), Matrix.one_apply_ne e0e2] at this
    exact this
  have h3 : M' e2 (fin0 hd2) * M (fin0 hd2) e2 = 1 := by
    have := congrFun (congrFun hM'M e2) e2
    rw [Matrix.mul_apply, Finset.sum_eq_single (fin0 hd2) (fun k _ hk => by rw [hcol2 k hk, mul_zero])
      (fun h => absurd (Finset.mem_univ _) h), Matrix.one_apply_eq] at this
    exact this
  have hz : M (fin0 hd2) e2 = 0 := by
    rcases mul_eq_zero.1 h2 with h4 | h4
    · rw [h4, zero_mul] at h1
      exact absurd h1 zero_ne_one
    · exact h4
  rw [hz, mul_zero] at h3
  exact zero_ne_one h3

theorem mu_eq_one_of_two {d : ℕ} (hd : d = 2) (h2 : (2 : K) = 0) (N : GL (Fin d) K) (s b : K) (μ : Kˣ)
    (h : N * tvGL (show 2 ≤ d by omega) s * N⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin d) μ * tvGL (show 2 ≤ d by omega) b) :
    μ = 1 := by
  subst hd
  have hR : Matrix.GeneralLinearGroup.scalar (Fin 2) μ * tvGL (show 2 ≤ 2 by omega) b ∈ slGL (Fin 2) K := by
    rw [← h]
    exact conj_mem_slGL N (tvGL_mem (show 2 ≤ 2 by omega) s)
  have hb : ((tvGL (show 2 ≤ 2 by omega) b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 :=
    mem_slGL.1 (tvGL_mem (show 2 ≤ 2 by omega) b)
  rw [mem_slGL, Units.val_mul, Matrix.det_mul, Matrix.GeneralLinearGroup.coe_scalar, scalar_eq_smul_one,
    Matrix.det_smul, Matrix.det_one, hb] at hR
  simp only [mul_one, Fintype.card_fin] at hR
  have hμ2 : ((μ : K) - 1) ^ 2 = 0 := by linear_combination hR + (1 - (μ : K)) * h2
  have h0 : (μ : K) - 1 = 0 := (pow_eq_zero_iff (two_ne_zero)).mp hμ2
  exact Units.ext (by rw [Units.val_one]; exact sub_eq_zero.mp h0)

theorem tau_apply_eq_of_conj_tv {d : ℕ} (hd : 2 ≤ d) (N : GL (Fin d) K) (τ : K ≃+* K)
    (h : ∀ b : K, N * tvGL hd (τ b) * N⁻¹ = tvGL hd b) (b : K) : τ b = b := by
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin d) (Fin d) K, M = (N : Matrix (Fin d) (Fin d) K) := ⟨_, rfl⟩
  obtain ⟨M', hM'⟩ : ∃ M' : Matrix (Fin d) (Fin d) K,
      M' = ((N⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := ⟨_, rfl⟩
  have hMM' : M * M' = 1 := by
    rw [hM, hM', ← Units.val_mul, mul_inv_cancel, Units.val_one]
  obtain ⟨E, hE⟩ : ∃ E : Matrix (Fin d) (Fin d) K, E = Matrix.single (fin0 hd) (fin1 hd) 1 := ⟨_, rfl⟩
  have hs : ∀ t : K, Matrix.single (fin0 hd) (fin1 hd) t = t • E := by
    intro t
    rw [hE]
    ext i j
    by_cases h1 : i = fin0 hd ∧ j = fin1 hd
    · obtain ⟨rfl, rfl⟩ := h1
      simp
    · simp [Matrix.single_apply, h1]
  have key : ∀ t : K, M * (1 + Matrix.single (fin0 hd) (fin1 hd) t) * M' = 1 + t • (M * E * M') := by
    intro t
    rw [hs t]
    calc M * (1 + t • E) * M' = M * M' + t • (M * E * M') := by
          simp [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, mul_assoc]
      _ = 1 + t • (M * E * M') := by rw [hMM']
  have hmat : ∀ t : K, M * (1 + Matrix.single (fin0 hd) (fin1 hd) (τ t)) * M' = 1 + Matrix.single (fin0 hd) (fin1 hd) t := by
    intro t
    have := congrArg (fun g : GL (Fin d) K => (g : Matrix (Fin d) (Fin d) K)) (h t)
    simp only [Units.val_mul, tvGL_coe] at this
    rw [hM, hM', ← this]
  have hQ : ∀ t : K, (τ t) • (M * E * M') = t • E := by
    intro t
    have := hmat t
    rw [key (τ t)] at this
    rw [hs t] at this
    exact add_left_cancel this
  have hQE : M * E * M' = E := by
    have h1 := hQ 1
    rw [map_one, one_smul, one_smul] at h1
    exact h1
  have h3 := hQ b
  rw [hQE] at h3
  have h4 := congrFun (congrFun h3 (fin0 hd)) (fin1 hd)
  rw [hE] at h4
  simpa [Matrix.smul_apply, Matrix.single_apply] using h4

theorem pow_mk_iterate {d : ℕ} (A : GL (Fin d) K) (σ : K ≃+* K)
    (u : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K)))
    (hβ : ∀ x : ↥(slGL (Fin d) K), u (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) x) =
      LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) (slTwist σ A x)) (k : ℕ) (x : ↥(slGL (Fin d) K)) :
    (u ^ k) (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) x) =
      LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) ((slTwist σ A)^[k] x) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, MulAut.mul_apply, hβ, ih, Function.iterate_succ_apply]

theorem iterate_eq_scalar_mul_of_pow {d : ℕ} (A : GL (Fin d) K) (σ : K ≃+* K) (p : ℕ)
    (u : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K)))
    (hβ : ∀ x : ↥(slGL (Fin d) K), u (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) x) =
      LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) (slTwist σ A x))
    (hpow : u ^ p = 1) (x : ↥(slGL (Fin d) K)) :
    ∃ c : Kˣ, (((slTwist σ A)^[p] x : ↥(slGL (Fin d) K)) : GL (Fin d) K) =
      Matrix.GeneralLinearGroup.scalar (Fin d) c * (x : GL (Fin d) K) := by
  have h1 : LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) ((slTwist σ A)^[p] x) =
      LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) x := by
    have h0 : (u ^ p) (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) x) =
        LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) x := by
      rw [hpow, MulAut.one_apply]
    rw [pow_mk_iterate A σ u hβ p x] at h0
    exact h0
  obtain ⟨c, hc⟩ := mk_eq_scalar _ _ h1
  refine ⟨c⁻¹, ?_⟩
  rw [hc, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

theorem units_eq_one_of_sq {K : Type} [Field K] (h2 : (2 : K) = 0) (c : Kˣ) (hc : (c : K) ^ 2 = 1) :
    c = 1 := by
  have hμ2 : ((c : K) - 1) ^ 2 = 0 := by linear_combination hc + (1 - (c : K)) * h2
  have h0 : (c : K) - 1 = 0 := (pow_eq_zero_iff two_ne_zero).mp hμ2
  exact Units.ext (by rw [Units.val_one]; exact sub_eq_zero.mp h0)

theorem sigma_pow_eq_one {d : ℕ} (hd : 2 ≤ d) (h2 : (2 : K) = 0) (A : GL (Fin d) K) (σ : K ≃+* K) (p : ℕ)
    (u : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K)))
    (hβ : ∀ x : ↥(slGL (Fin d) K), u (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) x) =
      LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) (slTwist σ A x))
    (hpow : u ^ p = 1) : σ ^ p = 1 := by
  have hb : ∀ b : K, normProd σ A p * tvGL hd ((σ ^ p) b) * (normProd σ A p)⁻¹ = tvGL hd b := by
    intro b
    set x : ↥(slGL (Fin d) K) := ⟨tvGL hd b, tvGL_mem hd b⟩ with hxdef
    have hx : (x : GL (Fin d) K) = tvGL hd b := rfl
    obtain ⟨c, hc⟩ := iterate_eq_scalar_mul_of_pow A σ p u hβ hpow x
    rw [hx] at hc
    have hcoe := coe_iterate_slTwist σ A p x
    rw [hx, glMap_tvGL hd (σ ^ p) b] at hcoe
    have hmain := hcoe.symm.trans hc
    have hc1 : c = 1 := by
      rcases (show d = 2 ∨ 3 ≤ d by omega) with h2d | h3d
      · exact mu_eq_one_of_two h2d h2 (normProd σ A p) ((σ ^ p) b) b c hmain
      · exact mu_eq_one_of_three_le h3d (normProd σ A p) ((σ ^ p) b) b c hmain
    rw [hc1, map_one, one_mul] at hmain
    exact hmain
  refine RingEquiv.ext (fun b => ?_)
  rw [tau_apply_eq_of_conj_tv hd (normProd σ A p) (σ ^ p) (fun b' => hb b') b]
  rfl

theorem normProd_scalar {d : ℕ} (hd : 2 ≤ d) (h2 : (2 : K) = 0) (A : GL (Fin d) K) (σ : K ≃+* K) (p : ℕ)
    (u : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K)))
    (hβ : ∀ x : ↥(slGL (Fin d) K), u (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) x) =
      LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) (slTwist σ A x))
    (hpow : u ^ p = 1) (hσ : σ ^ p = 1) :
    ∃ c : Kˣ, normProd σ A p = Matrix.GeneralLinearGroup.scalar (Fin d) c := by
  have hconj : ∀ x ∈ slGL (Fin d) K, ∃ c : Kˣ,
      normProd σ A p * x * (normProd σ A p)⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin d) c * x := by
    intro x hx
    set x' : ↥(slGL (Fin d) K) := ⟨x, hx⟩ with hx'
    have hx'' : (x' : GL (Fin d) K) = x := rfl
    obtain ⟨c, hc⟩ := iterate_eq_scalar_mul_of_pow A σ p u hβ hpow x'
    have hcoe := coe_iterate_slTwist σ A p x'
    rw [hσ, glMap_one, hx''] at hcoe
    rw [hx''] at hc
    exact ⟨c, hcoe.symm.trans hc⟩
  rcases (show d = 2 ∨ 3 ≤ d by omega) with h2d | h3d
  · subst h2d
    refine exists_scalar_of_commute_slGL _ (fun x hx => ?_)
    obtain ⟨c, hc⟩ := hconj x hx
    have hdet : ((Matrix.GeneralLinearGroup.scalar (Fin 2) c * x : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K).det = 1 := by
      rw [← hc]
      exact mem_slGL.1 (conj_mem_slGL _ hx)
    rw [Units.val_mul, Matrix.det_mul, Matrix.GeneralLinearGroup.coe_scalar, scalar_eq_smul_one,
      Matrix.det_smul, Matrix.det_one, mem_slGL.1 hx] at hdet
    simp only [mul_one, Fintype.card_fin] at hdet
    have hc1 : c = 1 := units_eq_one_of_sq h2 c hdet
    rw [hc, hc1, map_one, one_mul]
  · exact exists_scalar_of_conj_mod_scalar h3d _ hconj

theorem Ai_eq_smul_one_of_normProd {d : ℕ} (A : GL (Fin d) K) (σ : K ≃+* K) (p : ℕ)
    (hscalar : ∃ c : Kˣ, normProd σ A p = Matrix.GeneralLinearGroup.scalar (Fin d) c) :
    ∃ c : K, Ai σ (A : Matrix (Fin d) (Fin d) K) p = c • (1 : Matrix (Fin d) (Fin d) K) := by
  obtain ⟨c, hc⟩ := hscalar
  refine ⟨(c : K), ?_⟩
  rw [← coe_normProd, hc, Matrix.GeneralLinearGroup.coe_scalar, scalar_eq_smul_one]

end Transvection

end CFSG.LocalAnalysis.GLTheoremA.Y10GFldLinTw

end
