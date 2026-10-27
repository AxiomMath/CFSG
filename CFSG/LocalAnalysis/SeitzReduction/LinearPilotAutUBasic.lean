module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix CFSG.LocalAnalysis.ComponentInitial

variable {n : ℕ} {K : Type*} [Field K]

@[expose] def firstIdx (hn : 2 ≤ n) : Fin n := ⟨0, by omega⟩

@[expose] def lastIdx (hn : 2 ≤ n) : Fin n := ⟨n - 1, by omega⟩

theorem firstIdx_lt_lastIdx (hn : 2 ≤ n) : firstIdx hn < lastIdx hn :=
  Fin.mk_lt_mk.mpr (by omega)

theorem firstIdx_ne_lastIdx (hn : 2 ≤ n) : firstIdx hn ≠ lastIdx hn :=
  (firstIdx_lt_lastIdx hn).ne

theorem firstIdx_lt_of_ne (hn : 2 ≤ n) {k : Fin n} (hk : k ≠ firstIdx hn) : firstIdx hn < k := by
  rw [Fin.lt_def]
  have : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext h)
  simp only [firstIdx]
  omega

theorem lt_lastIdx_of_ne (hn : 2 ≤ n) {k : Fin n} (hk : k ≠ lastIdx hn) : k < lastIdx hn := by
  rw [Fin.lt_def]
  have : (k : ℕ) ≠ n - 1 := fun h => hk (Fin.ext h)
  have := k.isLt
  simp only [lastIdx]
  omega

theorem eq_one_of_one_add_eq_smul_conj (A : GL (Fin n) K) {M N : Matrix (Fin n) (Fin n) K}
    (hM : M * M = 0) (hN : N * N = 0) {k : Fin n} (hNk : N k k = 0) {c : K}
    (h : 1 + N = c • ((A : Matrix (Fin n) (Fin n) K) * (1 + M) *
      ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :
    c = 1 := by
  set B : Matrix (Fin n) (Fin n) K := ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hB
  set T : Matrix (Fin n) (Fin n) K := (A : Matrix (Fin n) (Fin n) K) * M * B with hTdef
  have hT : T * T = 0 := by
    calc T * T = (A : Matrix (Fin n) (Fin n) K) * M * (B * A) * M * B := by
          simp only [hTdef, Matrix.mul_assoc]
      _ = 0 := by
        rw [hB, Units.inv_mul, Matrix.mul_one, Matrix.mul_assoc (A : Matrix (Fin n) (Fin n) K) M M,
          hM, Matrix.mul_zero, Matrix.zero_mul]
  have hconj : (A : Matrix (Fin n) (Fin n) K) * (1 + M) * B = 1 + T := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hB, Units.mul_inv]
  rw [hconj, smul_add] at h
  have h3 : c • T = (1 - c) • (1 : Matrix (Fin n) (Fin n) K) + N := by
    rw [sub_smul, one_smul]
    calc c • T = (1 + N) - c • (1 : Matrix (Fin n) (Fin n) K) := by rw [h]; abel
      _ = _ := by abel
  have h2 : (c • T) * (c • T) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hT, smul_zero, smul_zero]
  rw [h3] at h2
  have h4 := congrFun (congrFun h2 k) k
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    hN, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, hNk,
    Matrix.zero_apply, smul_eq_mul, mul_one, mul_zero, add_zero] at h4
  have h5 : (1 - c) * (1 - c) = 0 := by linear_combination h4
  have h6 : 1 - c = 0 := mul_self_eq_zero.mp h5
  linear_combination -h6

theorem mul_eq_of_one_add_eq_smul_conj (A : GL (Fin n) K) {M N : Matrix (Fin n) (Fin n) K}
    (hM : M * M = 0) (hN : N * N = 0) {k : Fin n} (hNk : N k k = 0) {c : K}
    (h : 1 + N = c • ((A : Matrix (Fin n) (Fin n) K) * (1 + M) *
      ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :
    N * (A : Matrix (Fin n) (Fin n) K) = (A : Matrix (Fin n) (Fin n) K) * M := by
  rw [eq_one_of_one_add_eq_smul_conj A hM hN hNk h, one_smul, Matrix.mul_add, Matrix.mul_one,
    Matrix.add_mul, Units.mul_inv, add_right_inj] at h
  rw [h, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

theorem mul_eq_of_proj_eq (A : GL (Fin n) K) {x u : SpecialLinearGroup (Fin n) K}
    {M N : Matrix (Fin n) (Fin n) K}
    (hx : (x : Matrix (Fin n) (Fin n) K) = (A : Matrix (Fin n) (Fin n) K) * (1 + M) *
      ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hu : (u : Matrix (Fin n) (Fin n) K) = 1 + N) (hM : M * M = 0) (hN : N * N = 0) {k : Fin n}
    (hNk : N k k = 0) (h : LinearFlag.proj n K x = LinearFlag.proj n K u) :
    N * (A : Matrix (Fin n) (Fin n) K) = (A : Matrix (Fin n) (Fin n) K) * M := by
  obtain ⟨c, -, hc⟩ := LinearFlag.proj_eq_proj_iff.mp h
  have hux : (u : Matrix (Fin n) (Fin n) K) = (c : K) • (x : Matrix (Fin n) (Fin n) K) := by
    have hu' : u = x * (x⁻¹ * u) := by group
    rw [hu', Matrix.SpecialLinearGroup.coe_mul, hc, scalar_apply, ← smul_one_eq_diagonal,
      Matrix.mul_smul, Matrix.mul_one]
  rw [hu, hx] at hux
  exact mul_eq_of_one_add_eq_smul_conj A hM hN hNk hux

theorem single_mul_eq_of_conjAut_mul_fieldAut_apply (A : GL (Fin n) K) (σ : K ≃+* K)
    {i j : Fin n} (hij : i ≠ j) (c d : K)
    (h : (LinearFlag.conjAut n K A * LinearFlag.fieldAut n K σ)
        (LinearFlag.proj n K (SpecialLinearGroup.transvection hij c)) =
      LinearFlag.proj n K (SpecialLinearGroup.transvection hij d)) :
    single i j d * (A : Matrix (Fin n) (Fin n) K) =
      (A : Matrix (Fin n) (Fin n) K) * single i j (σ c) := by
  rw [MulAut.mul_apply, LinearFlag.fieldAut_proj, LinearFlag.conjAut_proj] at h
  refine mul_eq_of_proj_eq A ?_ (SpecialLinearGroup.transvection_coe hij d)
    (single_mul_single_of_ne _ _ _ _ hij.symm _) (single_mul_single_of_ne _ _ _ _ hij.symm _)
    (k := i) (single_apply_of_ne _ _ _ _ _ fun h => hij (h.1.trans h.2.symm)) h
  rw [LinearFlag.coe_slConjugation, SpecialLinearGroup.map_apply_coe,
    SpecialLinearGroup.transvection_coe]
  congr 2
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, single_apply, one_apply]
  split_ifs <;> simp

theorem single_mul_eq_of_conjAut_mul_fieldAut_mul_dualAut_apply (A : GL (Fin n) K)
    (σ : K ≃+* K) {i j : Fin n} (hij : i ≠ j) (c d : K)
    (h : (LinearFlag.conjAut n K A * LinearFlag.fieldAut n K σ * LinearFlag.dualAut n K)
        (LinearFlag.proj n K (SpecialLinearGroup.transvection hij c)) =
      LinearFlag.proj n K (SpecialLinearGroup.transvection hij d)) :
    single i j d * (A : Matrix (Fin n) (Fin n) K) =
      (A : Matrix (Fin n) (Fin n) K) * single j i (-σ c) := by
  rw [MulAut.mul_apply, MulAut.mul_apply, LinearFlag.dualAut_proj, LinearFlag.fieldAut_proj,
    LinearFlag.conjAut_proj] at h
  refine mul_eq_of_proj_eq A ?_ (SpecialLinearGroup.transvection_coe hij d)
    (single_mul_single_of_ne _ _ _ _ hij _) (single_mul_single_of_ne _ _ _ _ hij.symm _)
    (k := i) (single_apply_of_ne _ _ _ _ _ fun h => hij (h.1.trans h.2.symm)) h
  rw [LinearFlag.coe_slConjugation, SpecialLinearGroup.map_apply_coe,
    SpecialLinearGroup.coe_transpose, SpecialLinearGroup.transvection_inv,
    SpecialLinearGroup.transvection_coe, transpose_add, transpose_one, transpose_single]
  congr 2
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, single_apply, one_apply]
  split_ifs <;> simp

theorem eq_scalar_add_single_of_commute (hn : 2 ≤ n) {A : Matrix (Fin n) (Fin n) K}
    (h : ∀ i j : Fin n, i < j → Commute (single i j (1 : K)) A) :
    A = scalar (Fin n) (A (firstIdx hn) (firstIdx hn)) +
      single (firstIdx hn) (lastIdx hn) (A (firstIdx hn) (lastIdx hn)) := by
  set i₀ := firstIdx hn with hi₀
  set l := lastIdx hn with hl
  have hi₀l : i₀ ≠ l := firstIdx_ne_lastIdx hn
  ext k m
  have hsingle : single i₀ l (A i₀ l) k m = if i₀ = k ∧ l = m then A i₀ l else 0 :=
    single_apply _ _ _ _ _
  rw [Matrix.add_apply, scalar_apply, hsingle]
  by_cases hkm : k = m
  · subst hkm
    rw [diagonal_apply_eq, ite_eq_right (fun h => hi₀l (h.1.trans h.2.symm)), add_zero]
    by_cases hk : k = i₀
    · rw [hk]
    · exact (diag_eq_of_commute_single (h i₀ k (firstIdx_lt_of_ne hn hk))).symm
  · rw [diagonal_apply_ne _ hkm, zero_add]
    by_cases hk : k = i₀
    · subst hk
      by_cases hm : m = l
      · subst hm
        rw [ite_eq_left ⟨rfl, rfl⟩]
      · rw [ite_eq_right (fun h => hm h.2.symm)]
        exact col_eq_zero_of_commute_single (h m l (lt_lastIdx_of_ne hn hm)) hkm
    · rw [ite_eq_right (fun h => hk h.1.symm)]
      exact row_eq_zero_of_commute_single (h i₀ k (firstIdx_lt_of_ne hn hk)) (Ne.symm hkm)

theorem false_of_single_mul_eq_neg_mul_single (hn : 3 ≤ n) (A : GL (Fin n) K)
    (h : ∀ j : Fin n, ((j : ℕ) = 1 ∨ (j : ℕ) = 2) →
      single (⟨0, by omega⟩ : Fin n) j (1 : K) * (A : Matrix (Fin n) (Fin n) K) =
        -((A : Matrix (Fin n) (Fin n) K) * single j ⟨0, by omega⟩ 1)) : False := by
  set i₀ : Fin n := ⟨0, by omega⟩ with hi₀
  set j₁ : Fin n := ⟨1, by omega⟩ with hj₁
  set j₂ : Fin n := ⟨2, by omega⟩ with hj₂
  have h01 : i₀ ≠ j₁ := by simp [hi₀, hj₁, Fin.ext_iff]
  have h02 : i₀ ≠ j₂ := by simp [hi₀, hj₂, Fin.ext_iff]
  have h12 : j₁ ≠ j₂ := by simp [hj₁, hj₂, Fin.ext_iff]
  have hcol : ∀ j : Fin n, ((j : ℕ) = 1 ∨ (j : ℕ) = 2) → ∀ k : Fin n, k ≠ i₀ →
      (A : Matrix (Fin n) (Fin n) K) k j = 0 := by
    intro j hj k hk
    have e := congrFun (congrFun (h j hj) k) i₀
    rw [single_mul_apply_of_ne _ _ _ _ _ hk, Matrix.neg_apply, mul_single_apply_same, mul_one,
      zero_eq_neg] at e
    exact e
  set a : Matrix (Fin n) (Fin n) K := (A : Matrix (Fin n) (Fin n) K) with ha
  have hinj : ∀ v : Fin n → K, a *ᵥ v = 0 → v = 0 := fun v hv =>
    Matrix.eq_zero_of_mulVec_eq_zero (Matrix.GeneralLinearGroup.det_ne_zero A) hv
  set v : Fin n → K := Pi.single j₁ (a i₀ j₂) - Pi.single j₂ (a i₀ j₁) with hv
  have hAv : a *ᵥ v = 0 := by
    funext k
    simp only [hv, mulVec_sub, Pi.sub_apply, mulVec_single, Pi.smul_apply, col_apply,
      op_smul_eq_mul, Pi.zero_apply]
    by_cases hk : k = i₀
    · subst hk
      ring
    · rw [hcol j₁ (Or.inl rfl) k hk, hcol j₂ (Or.inr rfl) k hk]
      ring
  have hv0 := hinj v hAv
  have hb : a i₀ j₁ = 0 := by
    have := congrFun hv0 j₂
    rw [hv, Pi.sub_apply, Pi.single_eq_of_ne h12.symm, Pi.single_eq_same, zero_sub,
      Pi.zero_apply, neg_eq_zero] at this
    exact this
  have hcol1 : a *ᵥ Pi.single j₁ 1 = 0 := by
    funext k
    rw [mulVec_single_one, col_apply, Pi.zero_apply]
    by_cases hk : k = i₀
    · rw [hk, hb]
    · exact hcol j₁ (Or.inl rfl) k hk
  have := congrFun (hinj _ hcol1) j₁
  rw [Pi.single_eq_same, Pi.zero_apply] at this
  exact one_ne_zero this

end CFSG.SeitzReduction.LinearPilot
