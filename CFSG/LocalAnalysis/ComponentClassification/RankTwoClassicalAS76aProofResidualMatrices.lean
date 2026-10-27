module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSquareZero

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module

section Elements

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {r : ℕ}
  (b : Basis (Fin 2 ⊕ (Fin 2 ⊕ Fin r)) K V) (j₀ : Fin r)

@[expose] noncomputable def resU (k : Fin 2) : Module.End K V :=
  b.constr K fun x => if x = .inr (.inr j₀) then b (.inr (.inl k)) else 0

@[expose] noncomputable def resV (k : Fin 2) : Module.End K V :=
  b.constr K fun x => if x = .inl k then b (.inr (.inr j₀)) else 0

@[expose] noncomputable def resD : Module.End K V :=
  b.constr K fun x => match x with
    | .inl i => if i = 0 then b (.inl 1) else -b (.inl 0) - b (.inl 1)
    | .inr (.inl i) => if i = 0 then b (.inr (.inl 1)) else -b (.inr (.inl 0)) - b (.inr (.inl 1))
    | .inr (.inr j) => b (.inr (.inr j))

theorem resU_apply (k : Fin 2) (x : Fin 2 ⊕ (Fin 2 ⊕ Fin r)) :
    resU b j₀ k (b x) = if x = .inr (.inr j₀) then b (.inr (.inl k)) else 0 := by
  rw [resU, Basis.constr_basis]

theorem resV_apply (k : Fin 2) (x : Fin 2 ⊕ (Fin 2 ⊕ Fin r)) :
    resV b j₀ k (b x) = if x = .inl k then b (.inr (.inr j₀)) else 0 := by
  rw [resV, Basis.constr_basis]

@[simp] theorem resD_inl_zero : resD b (b (.inl 0)) = b (.inl 1) := by
  rw [resD, Basis.constr_basis]; rfl

@[simp] theorem resD_inl_one : resD b (b (.inl 1)) = -b (.inl 0) - b (.inl 1) := by
  rw [resD, Basis.constr_basis]; rfl

@[simp] theorem resD_inrl_zero : resD b (b (.inr (.inl 0))) = b (.inr (.inl 1)) := by
  rw [resD, Basis.constr_basis]; rfl

@[simp] theorem resD_inrl_one :
    resD b (b (.inr (.inl 1))) = -b (.inr (.inl 0)) - b (.inr (.inl 1)) := by
  rw [resD, Basis.constr_basis]; rfl

@[simp] theorem resD_inrr (j : Fin r) : resD b (b (.inr (.inr j))) = b (.inr (.inr j)) := by
  rw [resD, Basis.constr_basis]

theorem resD_cube : resD b ^ 3 = 1 := by
  apply b.ext
  rintro (i | i | j)
  · fin_cases i <;> simp [pow_succ, map_sub, map_neg] <;> abel
  · fin_cases i <;> simp [pow_succ, map_sub, map_neg] <;> abel
  · simp [pow_succ]

theorem resUD_cube (k : Fin 2) : ((1 + resU b j₀ k) * resD b) ^ 3 = 1 := by
  apply b.ext
  rintro (i | i | j)
  · fin_cases k <;> fin_cases i <;> simp [pow_succ, map_sub, map_neg, resU_apply] <;> abel
  · fin_cases k <;> fin_cases i <;> simp [pow_succ, map_sub, map_neg, resU_apply] <;> abel
  · by_cases hj : j = j₀
    · subst hj
      fin_cases k <;> simp [pow_succ, map_sub, map_neg, resU_apply] <;> abel
    · fin_cases k <;> simp [pow_succ, resU_apply, hj]

theorem resVD_cube (k : Fin 2) : ((1 + resV b j₀ k) * resD b) ^ 3 = 1 := by
  apply b.ext
  rintro (i | i | j)
  · fin_cases k <;> fin_cases i <;> simp [pow_succ, map_sub, map_neg, resV_apply] <;> abel
  · fin_cases k <;> fin_cases i <;> simp [pow_succ, map_sub, map_neg, resV_apply] <;> abel
  · fin_cases k <;> simp [pow_succ, resV_apply]

section Commute

variable {N : Module.End K V} (hN₁ : ∀ i, N (b (.inl i)) = b (.inr (.inl i)))
  (hN₂ : ∀ k, N (b (.inr k)) = 0)
include hN₁ hN₂

theorem resU_mul_comm (k : Fin 2) : resU b j₀ k * N = N * resU b j₀ k := by
  apply b.ext
  rintro (i | i | j)
  · simp [hN₁, resU_apply]
  · simp [hN₂, resU_apply]
  · by_cases hj : j = j₀
    · subst hj
      simp [hN₂, resU_apply]
    · simp [hN₂, resU_apply, hj]

theorem resV_mul_comm (k : Fin 2) : resV b j₀ k * N = N * resV b j₀ k := by
  apply b.ext
  rintro (i | i | j)
  · fin_cases k <;> fin_cases i <;> simp [hN₁, hN₂, resV_apply]
  · simp [hN₂, resV_apply]
  · simp [hN₂, resV_apply]

theorem resD_mul_comm : resD b * N = N * resD b := by
  apply b.ext
  rintro (i | i | j)
  · fin_cases i <;> simp [hN₁, map_sub, map_neg]
  · fin_cases i <;> simp [hN₂, map_sub, map_neg]
  · simp [hN₂]

theorem resC_mul :
    (1 + resU b j₀ 0 * resV b j₀ 0) * (1 + resU b j₀ 1 * resV b j₀ 1) = 1 + N := by
  apply b.ext
  rintro (i | i | j)
  · fin_cases i <;> simp [hN₁, resU_apply, resV_apply]
  · simp [hN₂, resV_apply]
  · simp [hN₂, resV_apply]

end Commute

theorem resC_comm :
    (1 + resU b j₀ 0 * resV b j₀ 0) * (1 + resU b j₀ 1 * resV b j₀ 1) =
      (1 + resU b j₀ 1 * resV b j₀ 1) * (1 + resU b j₀ 0 * resV b j₀ 0) := by
  apply b.ext
  rintro (i | i | j)
  · fin_cases i <;> simp [resU_apply, resV_apply]
  · simp [resV_apply]
  · simp [resV_apply]

section Two

variable [CharP K 2]

include K in
theorem two_zsmul_vec (v : V) : (2 : ℤ) • v = 0 := by
  rw [two_zsmul, ← two_smul K v, CharTwo.two_eq_zero, zero_smul]

include K in
theorem three_zsmul_vec (v : V) : (3 : ℤ) • v = v := by
  rw [show (3 : ℤ) = 2 + 1 by norm_num, add_zsmul, two_zsmul_vec (K := K), one_zsmul, zero_add]

theorem resU_sq (k : Fin 2) : (1 + resU b j₀ k) ^ 2 = 1 := by
  apply b.ext
  rintro (i | i | j)
  · simp [pow_succ, resU_apply]
  · simp [pow_succ, resU_apply]
  · by_cases hj : j = j₀
    · subst hj
      simp [pow_succ, resU_apply]
      abel_nf
      simp [two_zsmul_vec (K := K)]
    · simp [pow_succ, resU_apply, hj]

theorem resV_sq (k : Fin 2) : (1 + resV b j₀ k) ^ 2 = 1 := by
  apply b.ext
  rintro (i | i | j)
  · fin_cases k <;> fin_cases i <;> simp [pow_succ, resV_apply] <;> abel_nf <;>
      simp [two_zsmul_vec (K := K)]
  · simp [pow_succ, resV_apply]
  · simp [pow_succ, resV_apply]

theorem resUV_sq (k : Fin 2) :
    ((1 + resU b j₀ k) * (1 + resV b j₀ k)) ^ 2 = 1 + resU b j₀ k * resV b j₀ k := by
  apply b.ext
  rintro (i | i | j)
  · fin_cases k <;> fin_cases i <;> simp [pow_succ, resU_apply, resV_apply] <;> abel_nf <;>
      simp [two_zsmul_vec (K := K), three_zsmul_vec (K := K)]
  · simp [pow_succ, resU_apply, resV_apply]
  · by_cases hj : j = j₀
    · subst hj
      simp [pow_succ, resU_apply, resV_apply]
      abel_nf
      simp [two_zsmul_vec (K := K)]
    · simp [pow_succ, resU_apply, resV_apply, hj]

theorem resC_sq (k : Fin 2) : (1 + resU b j₀ k * resV b j₀ k) ^ 2 = 1 := by
  apply b.ext
  rintro (i | i | j)
  · fin_cases k <;> fin_cases i <;> simp [pow_succ, resU_apply, resV_apply] <;> abel_nf <;>
      simp [two_zsmul_vec (K := K)]
  · simp [pow_succ, resV_apply]
  · simp [pow_succ, resV_apply]

end Two

end Elements

theorem one_add_mul_comm {R : Type*} [Ring R] {x y : R} (h : x * y = y * x) :
    (1 + x) * (1 + y) = (1 + y) * (1 + x) :=
  ((Commute.one_left (1 + y)).add_left ((Commute.one_right x).add_right h)).eq

theorem exists_residual_elements {K : Type} [Field K] [CharP K 2] {n : ℕ} (hn : 5 ≤ n)
    (M : GL (Fin n) K)
    (hN : ((M : Matrix (Fin n) (Fin n) K) - 1) * ((M : Matrix (Fin n) (Fin n) K) - 1) = 0)
    (hr : ((M : Matrix (Fin n) (Fin n) K) - 1).rank = 2) :
    ∃ (u v : Fin 2 → GL (Fin n) K) (d : GL (Fin n) K),
      (∀ k, u k ^ 2 = 1) ∧ (∀ k, v k ^ 2 = 1) ∧ d ^ 3 = 1 ∧ (∀ k, (u k * d) ^ 3 = 1) ∧
      (∀ k, (v k * d) ^ 3 = 1) ∧ (∀ k, u k * M = M * u k) ∧ (∀ k, v k * M = M * v k) ∧
      d * M = M * d ∧ (∀ k, (u k * v k) ^ 4 = 1) ∧
      (u 0 * v 0) ^ 2 * (u 1 * v 1) ^ 2 = (u 1 * v 1) ^ 2 * (u 0 * v 0) ^ 2 ∧
      (u 0 * v 0) ^ 2 * (u 1 * v 1) ^ 2 = M := by
  classical
  set Nl := Matrix.toLin' ((M : Matrix (Fin n) (Fin n) K) - 1) with hNl
  have hNl2 : Nl ∘ₗ Nl = 0 := by rw [hNl, ← Matrix.toLin'_mul, hN, map_zero]
  have hrank : finrank K (LinearMap.range Nl) = 2 := by
    rw [← hr, Matrix.rank, hNl, Matrix.toLin'_apply']
  obtain ⟨r, b, hb1, hb2⟩ := exists_basis_sq_eq_zero Nl hNl2
  generalize hℓdef : finrank K (LinearMap.range Nl) = ℓ at b hb1 hb2
  rw [hrank] at hℓdef
  subst hℓdef
  have hcard := Module.finrank_eq_card_basis b
  rw [Module.finrank_fin_fun, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_fin] at hcard
  set j₀ : Fin r := ⟨0, by omega⟩
  let ψ := Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := K)
  have hM : ((ψ M : (Module.End K (Fin n → K))ˣ) : Module.End K (Fin n → K)) = 1 + Nl := by
    rw [Matrix.GeneralLinearGroup.coe_toLin, hNl, map_sub, Matrix.toLin'_apply',
      Matrix.toLin'_one, ← Module.End.one_eq_id, add_sub_cancel]
  let u' : Fin 2 → (Module.End K (Fin n → K))ˣ := fun k =>
    Units.ofPowEqOne _ 2 (resU_sq b j₀ k) two_ne_zero
  let v' : Fin 2 → (Module.End K (Fin n → K))ˣ := fun k =>
    Units.ofPowEqOne _ 2 (resV_sq b j₀ k) two_ne_zero
  let d' : (Module.End K (Fin n → K))ˣ := Units.ofPowEqOne _ 3 (resD_cube b) three_ne_zero
  have hu' : ∀ k, ((u' k : (Module.End K (Fin n → K))ˣ) : Module.End K (Fin n → K)) =
      1 + resU b j₀ k := fun k => Units.val_ofPowEqOne _ _ _ _
  have hv' : ∀ k, ((v' k : (Module.End K (Fin n → K))ˣ) : Module.End K (Fin n → K)) =
      1 + resV b j₀ k := fun k => Units.val_ofPowEqOne _ _ _ _
  have hd' : ((d' : (Module.End K (Fin n → K))ˣ) : Module.End K (Fin n → K)) = resD b :=
    Units.val_ofPowEqOne _ _ _ _
  have hMM : M = ψ.symm (ψ M) := (ψ.symm_apply_apply M).symm
  refine ⟨fun k => ψ.symm (u' k), fun k => ψ.symm (v' k), ψ.symm d', fun k => ?_, fun k => ?_,
    ?_, fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_, ?_, fun k => ?_, ?_, ?_⟩
  · rw [← map_pow, Units.pow_ofPowEqOne, map_one]
  · rw [← map_pow, Units.pow_ofPowEqOne, map_one]
  · rw [← map_pow, Units.pow_ofPowEqOne, map_one]
  · rw [← map_mul, ← map_pow, ← map_one ψ.symm]
    congr 1
    ext1
    rw [Units.val_pow_eq_pow_val, Units.val_mul, hu', hd', Units.val_one]
    exact resUD_cube b j₀ k
  · rw [← map_mul, ← map_pow, ← map_one ψ.symm]
    congr 1
    ext1
    rw [Units.val_pow_eq_pow_val, Units.val_mul, hv', hd', Units.val_one]
    exact resVD_cube b j₀ k
  · rw [hMM, ← map_mul, ← map_mul]
    congr 1
    ext1
    rw [Units.val_mul, Units.val_mul, hu', hM]
    exact one_add_mul_comm (resU_mul_comm b j₀ hb1 hb2 k)
  · rw [hMM, ← map_mul, ← map_mul]
    congr 1
    ext1
    rw [Units.val_mul, Units.val_mul, hv', hM]
    exact one_add_mul_comm (resV_mul_comm b j₀ hb1 hb2 k)
  · rw [hMM, ← map_mul, ← map_mul]
    congr 1
    ext1
    rw [Units.val_mul, Units.val_mul, hd', hM, mul_add, add_mul, mul_one, one_mul,
      resD_mul_comm b hb1 hb2]
  · rw [← map_mul, ← map_pow, ← map_one ψ.symm]
    congr 1
    ext1
    rw [Units.val_pow_eq_pow_val, Units.val_mul, hu', hv', Units.val_one,
      show 4 = 2 * 2 by rfl, pow_mul, resUV_sq, resC_sq]
  · simp only [← map_mul, ← map_pow]
    congr 1
    ext1
    rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
      Units.val_mul, Units.val_mul, hu', hv', hu', hv', resUV_sq, resUV_sq]
    exact resC_comm b j₀
  · rw [hMM, ← map_mul, ← map_mul, ← map_pow, ← map_pow, ← map_mul]
    congr 1
    ext1
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_mul,
      Units.val_mul, hu', hv', hu', hv', resUV_sq, resUV_sq, hM]
    exact resC_mul b j₀ hb1 hb2

end CFSG.ComponentClassification.RankTwoClassical
