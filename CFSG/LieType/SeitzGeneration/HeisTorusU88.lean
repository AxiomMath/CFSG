module

public import CFSG.LieType.SeitzGeneration.HeisTorusUDefs
public import CFSG.LieType.SeitzGeneration.HeisTorusIdent
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {K : Type} [Field K]

@[expose] def ug88_z (ζ : K) (n : ℕ) : K := ζ ^ (n % 5)

@[expose] def ug88_Phi (ζ : K) : Matrix (Fin 5) (Fin 5) K := heisFourierMat ζ

@[expose] def ug88_Psi (ζ : K) : Matrix (Fin 5) (Fin 5) K :=
  Matrix.of fun i j => ζ ^ (4 * ((i : ℕ) * (j : ℕ)))

@[expose] def ug88_ent (ζ : K) (i j : Fin 5) : Fin 5 → K :=
  fun k => if k = i then ζ else if k = j then ζ ^ 4 else 1

@[expose] def ug88_Bm (ζ : K) (i j : Fin 5) : Matrix (Fin 5) (Fin 5) K :=
  ug88_Phi ζ * diagonal (ug88_ent ζ i j) * ug88_Psi ζ

theorem ug88_z_eq {ζ : K} (hζ5 : ζ ^ 5 = 1) (n : ℕ) : ug88_z ζ n = ζ ^ n := by
  unfold ug88_z
  conv_rhs => rw [← Nat.mod_add_div n 5, pow_add, pow_mul, hζ5, one_pow, mul_one]

theorem ug88_inv_pow {ζ : K} (hζ5 : ζ ^ 5 = 1) (n : ℕ) : (ζ ^ n)⁻¹ = ζ ^ (4 * n) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← pow_add, show n + 4 * n = 5 * n by ring, pow_mul, hζ5, one_pow]

theorem ug88_natCast_five (h2 : (2 : K) = 0) : ((5 : ℕ) : K) = 1 := by
  push_cast
  linear_combination 2 * h2

theorem ug88_Phi_mul_Psi {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (h2 : (2 : K) = 0) :
    ug88_Phi ζ * ug88_Psi ζ = 1 := by
  have hΨ : ug88_Psi ζ = Matrix.of fun i j : Fin 5 =>
      ((5 : ℕ) : K)⁻¹ * (ζ ^ ((i : ℕ) * (j : ℕ)))⁻¹ := by
    ext i j
    simp only [ug88_Psi, of_apply, ug88_natCast_five h2, inv_one, one_mul,
      ug88_inv_pow hζ.pow_eq_one]
  rw [hΨ]
  exact heisFourierMat_mul_inv_entries hζ (by norm_num)

theorem ug88_Psi_mul_Phi {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (h2 : (2 : K) = 0) :
    ug88_Psi ζ * ug88_Phi ζ = 1 :=
  mul_eq_one_comm.mp (ug88_Phi_mul_Psi hζ h2)

theorem ug88_Phi_transpose (ζ : K) : (ug88_Phi ζ)ᵀ = ug88_Phi ζ := by
  ext i j
  simp [ug88_Phi, heisFourierMat, Nat.mul_comm]

theorem ug88_Psi_transpose (ζ : K) : (ug88_Psi ζ)ᵀ = ug88_Psi ζ := by
  ext i j
  simp [ug88_Psi, Nat.mul_comm]

theorem ug88_bar (h : UnitaryFieldData 2 2 K) (c : K) : h.bar c = c ^ 4 := by
  rw [UnitaryFieldData.bar_apply]
  norm_num

theorem ug88_pow_four_mul {ζ : K} (hζ5 : ζ ^ 5 = 1) (m : ℕ) :
    (ζ ^ (4 * m)) ^ 4 = ζ ^ m := by
  rw [← pow_mul, show 4 * m * 4 = m + 5 * (3 * m) by ring, pow_add, pow_mul, hζ5, one_pow,
    mul_one]

theorem ug88_Phi_map_bar (h : UnitaryFieldData 2 2 K) (ζ : K) :
    (ug88_Phi ζ).map h.bar = ug88_Psi ζ := by
  ext i j
  simp only [ug88_Phi, heisFourierMat, ug88_Psi, of_apply, map_apply, ug88_bar]
  rw [← pow_mul, Nat.mul_comm]

theorem ug88_Psi_map_bar (h : UnitaryFieldData 2 2 K) {ζ : K} (hζ5 : ζ ^ 5 = 1) :
    (ug88_Psi ζ).map h.bar = ug88_Phi ζ := by
  ext i j
  simp only [ug88_Phi, heisFourierMat, ug88_Psi, of_apply, map_apply, ug88_bar]
  exact ug88_pow_four_mul hζ5 _

theorem ug88_diag_mul_eq_one {d e : Fin 5 → K} (h : ∀ k, d k * e k = 1) :
    diagonal d * diagonal e = 1 := by
  rw [diagonal_mul_diagonal]
  have hfun : (fun k => d k * e k) = fun _ => (1 : K) := funext h
  rw [hfun]
  exact diagonal_one

theorem ug88_sandwich_one {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (h2 : (2 : K) = 0) {f : Fin 5 → K}
    (hf : ∀ k, f k = 1) : ug88_Phi ζ * diagonal f * ug88_Psi ζ = 1 := by
  have hdiag : diagonal f = 1 := by
    have hf1 : f = 1 := funext hf
    rw [hf1]
    exact diagonal_one
  rw [hdiag, Matrix.mul_one, ug88_Phi_mul_Psi hζ h2]

theorem ug88_conj_mul_diag {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (h2 : (2 : K) = 0)
    (d e : Fin 5 → K) :
    (ug88_Phi ζ * diagonal d * ug88_Psi ζ) * (ug88_Phi ζ * diagonal e * ug88_Psi ζ) =
      ug88_Phi ζ * diagonal (fun k => d k * e k) * ug88_Psi ζ := by
  have hΨΦ := ug88_Psi_mul_Phi hζ h2
  calc ug88_Phi ζ * diagonal d * ug88_Psi ζ *
        (ug88_Phi ζ * diagonal e * ug88_Psi ζ)
      = ug88_Phi ζ * diagonal d * (ug88_Psi ζ * ug88_Phi ζ) * diagonal e *
          ug88_Psi ζ := by simp only [Matrix.mul_assoc]
    _ = ug88_Phi ζ * (diagonal d * diagonal e) * ug88_Psi ζ := by
          rw [hΨΦ]
          simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = ug88_Phi ζ * diagonal (fun k => d k * e k) * ug88_Psi ζ := by
          rw [diagonal_mul_diagonal]

theorem ug88_transpose_sandwich (ζ : K) (d : Fin 5 → K) :
    (ug88_Psi ζ * diagonal d * ug88_Phi ζ)ᵀ =
      ug88_Phi ζ * diagonal d * ug88_Psi ζ := by
  rw [transpose_mul, transpose_mul, diagonal_transpose, ug88_Phi_transpose, ug88_Psi_transpose]
  simp only [Matrix.mul_assoc]

theorem ug88_ent_pow {ζ : K} (hζ5 : ζ ^ 5 = 1) (i j k : Fin 5) :
    ug88_ent ζ i j k ^ 5 = 1 := by
  unfold ug88_ent
  split_ifs
  · exact hζ5
  · rw [← pow_mul, mul_comm, pow_mul, hζ5, one_pow]
  · exact one_pow 5

theorem ug88_ent_mul {ζ : K} (hζ5 : ζ ^ 5 = 1) {i j : Fin 5} (hij : i ≠ j) (k : Fin 5) :
    ug88_ent ζ i j k * ug88_ent ζ j i k = 1 := by
  unfold ug88_ent
  by_cases hki : k = i
  · subst hki
    simp [hij]
    linear_combination hζ5
  · by_cases hkj : k = j
    · subst hkj
      simp [hki]
      linear_combination hζ5
    · simp [hki, hkj]

theorem ug88_ent_prod {ζ : K} (hζ5 : ζ ^ 5 = 1) {i j : Fin 5} (hij : i ≠ j) :
    ∏ k, ug88_ent ζ i j k = 1 := by
  fin_cases i <;> fin_cases j <;> first
    | exact absurd rfl hij
    | (simp [ug88_ent, Fin.prod_univ_five]; linear_combination hζ5)

@[expose] noncomputable def ug88_diagGL {d : Fin 5 → K} (hd : ∀ k, d k ^ 5 = 1) :
    GL (Fin 5) K :=
  Units.mk (diagonal d) (diagonal fun k => d k ^ 4)
    (ug88_diag_mul_eq_one fun k => by
      show d k * d k ^ 4 = 1
      rw [show d k * d k ^ 4 = d k ^ 5 by ring, hd k])
    (ug88_diag_mul_eq_one fun k => by
      show d k ^ 4 * d k = 1
      rw [show d k ^ 4 * d k = d k ^ 5 by ring, hd k])

@[expose] noncomputable def ug88_conjGL {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (h2 : (2 : K) = 0)
    {d : Fin 5 → K} (hd : ∀ k, d k ^ 5 = 1) : GL (Fin 5) K :=
  Units.mk (ug88_Phi ζ * diagonal d * ug88_Psi ζ)
    (ug88_Phi ζ * diagonal (fun k => d k ^ 4) * ug88_Psi ζ)
    (by
      rw [ug88_conj_mul_diag hζ h2]
      exact ug88_sandwich_one hζ h2 fun k => by
        show d k * d k ^ 4 = 1
        rw [show d k * d k ^ 4 = d k ^ 5 by ring, hd k])
    (by
      rw [ug88_conj_mul_diag hζ h2]
      exact ug88_sandwich_one hζ h2 fun k => by
        show d k ^ 4 * d k = 1
        rw [show d k ^ 4 * d k = d k ^ 5 by ring, hd k])

theorem ug88_diagGL_mem (h : UnitaryFieldData 2 2 K) {d : Fin 5 → K} (hd : ∀ k, d k ^ 5 = 1)
    (hdet : ∏ k, d k = 1) : ug88_diagGL hd ∈ unitarySU 2 2 K 5 := by
  rw [mem_unitarySU_iff h]
  refine ⟨?_, ?_⟩
  · show (diagonal d).det = 1
    rw [det_diagonal, hdet]
  · show ((diagonal d).map h.bar)ᵀ * diagonal d = 1
    rw [diagonal_map (map_zero h.bar), diagonal_transpose]
    exact ug88_diag_mul_eq_one fun k => by
      show h.bar (d k) * d k = 1
      rw [ug88_bar, show d k ^ 4 * d k = d k ^ 5 by ring, hd k]

theorem ug88_conjGL_mem (h : UnitaryFieldData 2 2 K) {ζ : K} (hζ : IsPrimitiveRoot ζ 5)
    (h2 : (2 : K) = 0) {d : Fin 5 → K} (hd : ∀ k, d k ^ 5 = 1) (hdet : ∏ k, d k = 1) :
    ug88_conjGL hζ h2 hd ∈ unitarySU 2 2 K 5 := by
  rw [mem_unitarySU_iff h]
  refine ⟨?_, ?_⟩
  · show (ug88_Phi ζ * diagonal d * ug88_Psi ζ).det = 1
    have hdet' : (ug88_Phi ζ).det * (ug88_Psi ζ).det = 1 := by
      rw [← det_mul, ug88_Phi_mul_Psi hζ h2, det_one]
    rw [det_mul, det_mul, det_diagonal, hdet, mul_one]
    linear_combination hdet'
  · show ((ug88_Phi ζ * diagonal d * ug88_Psi ζ).map h.bar)ᵀ *
      (ug88_Phi ζ * diagonal d * ug88_Psi ζ) = 1
    have hD : (diagonal d).map h.bar = diagonal (fun k => d k ^ 4) := by
      rw [diagonal_map (map_zero h.bar)]
      exact congrArg diagonal (funext fun k => ug88_bar h (d k))
    rw [Matrix.map_mul, Matrix.map_mul, ug88_Phi_map_bar h ζ, hD,
      ug88_Psi_map_bar h (ζ := ζ) hζ.pow_eq_one, ug88_transpose_sandwich, ug88_conj_mul_diag hζ h2]
    exact ug88_sandwich_one hζ h2 fun k => by
      show d k ^ 4 * d k = 1
      rw [show d k ^ 4 * d k = d k ^ 5 by ring, hd k]

theorem ug88_conjGL_tw {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (h2 : (2 : K) = 0) {d : Fin 5 → K}
    (hd : ∀ k, d k ^ 5 = 1) :
    (ug88_conjGL hζ h2 hd : Matrix (Fin 5) (Fin 5) K) * ug88_Phi ζ =
      ug88_Phi ζ * diagonal d := by
  show ug88_Phi ζ * diagonal d * ug88_Psi ζ * ug88_Phi ζ =
    ug88_Phi ζ * diagonal d
  rw [Matrix.mul_assoc (ug88_Phi ζ * diagonal d), ug88_Psi_mul_Phi hζ h2, Matrix.mul_one]

theorem ug88_Phi_mulVec_single (ζ : K) (i a : Fin 5) :
    (ug88_Phi ζ *ᵥ Pi.single i 1) a = ζ ^ ((a : ℕ) * (i : ℕ)) := by
  simp [mulVec, dotProduct, ug88_Phi, heisFourierMat, Pi.single_apply]

theorem ug88_diag_mulVec_eq {ζ : K} {i j : Fin 5} (hij : i ≠ j) (w : Fin 5 → K) :
    diagonal (ug88_ent ζ i j) *ᵥ w =
      w + ((ζ - 1) * w i) • Pi.single i 1 + ((ζ ^ 4 - 1) * w j) • Pi.single j 1 := by
  funext k
  by_cases hki : k = i
  · subst hki
    simp [ug88_ent, mulVec_diagonal, Pi.single_apply, hij]
    ring
  · by_cases hkj : k = j
    · subst hkj
      simp [ug88_ent, mulVec_diagonal, Pi.single_apply, hki, hij.symm]
      ring
    · simp [ug88_ent, mulVec_diagonal, Pi.single_apply, hki, hkj]

theorem ug88_Bm_mulVec {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (h2 : (2 : K) = 0) {i j : Fin 5}
    (hij : i ≠ j) (v : Fin 5 → K) :
    ug88_Bm ζ i j *ᵥ v = fun a => v a + (ζ - 1) *
        (∑ b : Fin 5, ug88_z ζ (4 * ((i : ℕ) * (b : ℕ))) * v b) * ug88_z ζ ((a : ℕ) * (i : ℕ)) +
      (ζ ^ 4 - 1) * (∑ b : Fin 5, ug88_z ζ (4 * ((j : ℕ) * (b : ℕ))) * v b) *
        ug88_z ζ ((a : ℕ) * (j : ℕ)) := by
  have hΦw : ug88_Phi ζ *ᵥ (ug88_Psi ζ *ᵥ v) = v := by
    rw [mulVec_mulVec, ug88_Phi_mul_Psi hζ h2, one_mulVec]
  have key : ug88_Bm ζ i j *ᵥ v =
      ug88_Phi ζ *ᵥ (diagonal (ug88_ent ζ i j) *ᵥ (ug88_Psi ζ *ᵥ v)) := by
    rw [ug88_Bm, ← mulVec_mulVec, ← mulVec_mulVec]
  funext a
  rw [key, ug88_diag_mulVec_eq hij, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, hΦw]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ug88_Phi_mulVec_single,
    ug88_z_eq hζ.pow_eq_one]
  simp only [mulVec, dotProduct, ug88_Psi, of_apply]

@[expose] def ug88_w1 (ζ : K) : Fin 5 → K := ![ζ ^ 2 + ζ ^ 3, ζ, 0, ζ ^ 3, 1 + ζ ^ 3]

@[expose] def ug88_w2 (ζ : K) : Fin 5 → K := ![ζ ^ 3, 1 + ζ ^ 3, ζ ^ 2 + ζ ^ 3, ζ, 0]

@[expose] def ug88_w3 (ζ : K) : Fin 5 → K :=
  ![0, ζ ^ 2 + ζ ^ 3, ζ ^ 2, 1 + ζ + ζ ^ 2 + ζ ^ 3, 1 + ζ ^ 2]

macro "ug88_simp" : tactic =>
  `(tactic| simp (config := { decide := true }) only [
    Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, Fin.mk_one, cons_val_zero, head_cons, ug88_z,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod, Fin.sum_univ_five, Nat.zero_mod, mul_zero, pow_zero,
      mul_one, Nat.one_mod, Nat.reduceMul, cons_val_one, add_zero, pow_one, cons_val,
      Nat.mod_succ, zero_mul, add_sub_cancel, one_mul, ug88_w1, ug88_w2, ug88_w3,
      mulVec_diagonal, ug88_ent, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ↓reduceIte
  ])

theorem ug88_stage1 {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (h2 : (2 : K) = 0)
    (hΦ : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0) :
    ug88_Bm ζ 2 0 *ᵥ ![1, 0, 0, 0, 0] = ug88_w1 ζ := by
  rw [ug88_Bm_mulVec hζ h2 (by decide)]
  funext a
  fin_cases a
  · ug88_simp
    linear_combination (1 : K) * hΦ + (-ζ ^ 3 - ζ ^ 2 - 1) * h2
  · ug88_simp
    linear_combination (1 : K) * hΦ + (-ζ ^ 2 - ζ - 1) * h2
  · ug88_simp
    linear_combination (ζ - 1) * hΦ
  · ug88_simp
    linear_combination (1 : K) * hΦ + (-ζ ^ 3 - ζ - 1) * h2
  · ug88_simp
    linear_combination (2 : K) * hΦ + (-2 * ζ ^ 3 - ζ ^ 2 - ζ - 2) * h2

theorem ug88_stage2 {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (h2 : (2 : K) = 0)
    (hΦ : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0) :
    ug88_Bm ζ 2 0 *ᵥ ![0, 0, 1, 0, 0] = ug88_w2 ζ := by
  rw [ug88_Bm_mulVec hζ h2 (by decide)]
  funext a
  fin_cases a
  · ug88_simp
    linear_combination (1 : K) * hΦ + (-ζ ^ 3 - ζ - 1) * h2
  · ug88_simp
    linear_combination (2 : K) * hΦ + (-2 * ζ ^ 3 - ζ ^ 2 - ζ - 2) * h2
  · ug88_simp
    linear_combination (ζ ^ 2 - 2 * ζ + 2) * hΦ + (-ζ ^ 3 - ζ ^ 2 - 1) * h2
  · ug88_simp
    linear_combination (1 : K) * hΦ + (-ζ ^ 2 - ζ - 1) * h2
  · ug88_simp
    linear_combination (ζ - 1) * hΦ

theorem ug88_stage3 {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (h2 : (2 : K) = 0)
    (hΦ : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0) :
    ug88_Bm ζ 0 4 *ᵥ ![0, 1, 0, 0, 0] = ug88_w3 ζ := by
  rw [ug88_Bm_mulVec hζ h2 (by decide)]
  funext a
  fin_cases a
  · ug88_simp
    linear_combination (ζ - 1) * hΦ
  · ug88_simp
    linear_combination (ζ ^ 5 - ζ ^ 4 - ζ + 2) * hΦ + (-ζ ^ 3 - ζ ^ 2 - 1) * h2
  · ug88_simp
    linear_combination (ζ ^ 4 - ζ ^ 3 - 1) * hΦ + (ζ ^ 3 + ζ) * h2
  · ug88_simp
    linear_combination (ζ ^ 3 - ζ ^ 2) * hΦ + (-ζ ^ 3 - 1) * h2
  · ug88_simp
    linear_combination (ζ ^ 2 - ζ) * hΦ + (-ζ ^ 2 + ζ - 1) * h2

theorem ug88_final_Y0_1 {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (h2 : (2 : K) = 0)
    (hΦ : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0) :
    (ug88_Bm ζ 4 0 *ᵥ (diagonal (ug88_ent ζ 2 1) *ᵥ ug88_w1 ζ)) 1 = 0 := by
  rw [ug88_Bm_mulVec hζ h2 (by decide)]
  ug88_simp
  linear_combination
    (ζ ^ 8 - 3 * ζ ^ 6 + 4 * ζ ^ 5 - 2 * ζ ^ 4 + 4 * ζ ^ 3
      - 3 * ζ ^ 2 - 3 * ζ + 5) * hΦ +
    (-3 * ζ ^ 3 - ζ - 3) * h2

theorem ug88_final_Y0_2 {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (h2 : (2 : K) = 0)
    (hΦ : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0) :
    (ug88_Bm ζ 4 0 *ᵥ (diagonal (ug88_ent ζ 2 1) *ᵥ ug88_w1 ζ)) 2 = 0 := by
  rw [ug88_Bm_mulVec hζ h2 (by decide)]
  ug88_simp
  linear_combination (ζ ^ 7 - 2 * ζ ^ 5 + 2 * ζ ^ 4 + 2 * ζ ^ 3 - ζ ^ 2 - 3 * ζ + 1) * hΦ +
    (-ζ ^ 3 + ζ ^ 2 + ζ - 1) * h2

theorem ug88_final_Y2_2 {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (h2 : (2 : K) = 0)
    (hΦ : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0) :
    (ug88_Bm ζ 4 0 *ᵥ (diagonal (ug88_ent ζ 2 1) *ᵥ ug88_w2 ζ)) 2 = 0 := by
  rw [ug88_Bm_mulVec hζ h2 (by decide)]
  ug88_simp
  linear_combination (ζ ^ 8 - ζ ^ 7 + ζ ^ 6 + ζ ^ 3 - 3 * ζ ^ 2 + 3 * ζ - 2) * hΦ +
    (ζ ^ 2 - ζ + 1) * h2

theorem ug88_final_Y2_1 {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (h2 : (2 : K) = 0)
    (hΦ : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0) :
    (ζ - 1) * (ug88_Bm ζ 4 0 *ᵥ (diagonal (ug88_ent ζ 2 1) *ᵥ ug88_w2 ζ)) 1 = 1 := by
  rw [ug88_Bm_mulVec hζ h2 (by decide)]
  ug88_simp
  linear_combination
    (ζ ^ 10 - 3 * ζ ^ 9 + 5 * ζ ^ 8 - 4 * ζ ^ 7 - ζ ^ 6 + 6 * ζ ^ 5
      - 7 * ζ ^ 4 + 5 * ζ ^ 3 - 2 * ζ ^ 2 - 4 * ζ + 7) * hΦ +
    (-2 * ζ ^ 3 - ζ ^ 2 - ζ - 4) * h2

theorem ug88_final_X1_1 {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (h2 : (2 : K) = 0)
    (hΦ : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0) :
    (ug88_Bm ζ 0 2 *ᵥ (diagonal (ug88_ent ζ 1 2) *ᵥ ug88_w3 ζ)) 1 = (ζ + 1) ^ 3 := by
  rw [ug88_Bm_mulVec hζ h2 (by decide)]
  ug88_simp
  linear_combination
    (3 * ζ ^ 9 - ζ ^ 8 - ζ ^ 7 + ζ ^ 6 - 5 * ζ ^ 5 + 5 * ζ ^ 4
      - 4 * ζ ^ 2 + 5 * ζ - 5) * hΦ +
    (2 * ζ ^ 3 - ζ + 1) * h2

theorem ug88_final_X1_3 {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (h2 : (2 : K) = 0)
    (hΦ : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0) :
    (ug88_Bm ζ 0 2 *ᵥ (diagonal (ug88_ent ζ 1 2) *ᵥ ug88_w3 ζ)) 3 = ζ := by
  rw [ug88_Bm_mulVec hζ h2 (by decide)]
  ug88_simp
  linear_combination
    (3 * ζ ^ 8 - ζ ^ 7 - ζ ^ 6 + ζ ^ 5 - 5 * ζ ^ 4
      + 6 * ζ ^ 3 - 3 * ζ ^ 2 + 3) * hΦ +
    (-3 * ζ ^ 3 - ζ - 2) * h2

@[expose] noncomputable def ug88_Rg {ζ : K} (hζ5 : ζ ^ 5 = 1) (i j : Fin 5) : GL (Fin 5) K :=
  ug88_diagGL (ug88_ent_pow hζ5 i j)

@[expose] noncomputable def ug88_Bg {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (h2 : (2 : K) = 0)
    (i j : Fin 5) : GL (Fin 5) K :=
  ug88_conjGL hζ h2 (ug88_ent_pow hζ.pow_eq_one i j)

@[expose] noncomputable def ug88_x {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (h2 : (2 : K) = 0) :
    GL (Fin 5) K :=
  ug88_Bg hζ h2 0 2 * ug88_Rg hζ.pow_eq_one 1 2 * ug88_Bg hζ h2 0 4

@[expose] noncomputable def ug88_y {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (h2 : (2 : K) = 0) :
    GL (Fin 5) K :=
  ug88_Bg hζ h2 4 0 * ug88_Rg hζ.pow_eq_one 2 1 * ug88_Bg hζ h2 2 0

@[expose] noncomputable def ug88_g {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (h2 : (2 : K) = 0) :
    GL (Fin 5) K :=
  ug88_x hζ h2 * ug88_Rg hζ.pow_eq_one 1 2 * ug88_y hζ h2

theorem ug88_Bg_mul_Bg {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (h2 : (2 : K) = 0) {i j : Fin 5}
    (hij : i ≠ j) : ug88_Bg hζ h2 i j * ug88_Bg hζ h2 j i = 1 := by
  apply Units.ext
  rw [Units.val_mul]
  show (ug88_Phi ζ * diagonal (ug88_ent ζ i j) * ug88_Psi ζ) *
    (ug88_Phi ζ * diagonal (ug88_ent ζ j i) * ug88_Psi ζ) = 1
  exact (ug88_conj_mul_diag hζ h2 _ _).trans
    (ug88_sandwich_one hζ h2 fun k => ug88_ent_mul hζ.pow_eq_one hij k)

theorem ug88_Rg_mul_Rg {ζ : K} (hζ5 : ζ ^ 5 = 1) {i j : Fin 5} (hij : i ≠ j) :
    ug88_Rg hζ5 i j * ug88_Rg hζ5 j i = 1 := by
  apply Units.ext
  rw [Units.val_mul]
  show diagonal (ug88_ent ζ i j) * diagonal (ug88_ent ζ j i) = 1
  exact ug88_diag_mul_eq_one fun k => ug88_ent_mul hζ5 hij k

theorem ug88_x_mul_y {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (h2 : (2 : K) = 0) :
    ug88_x hζ h2 * ug88_y hζ h2 = 1 := by
  have h1 : ug88_Bg hζ h2 0 4 * ug88_Bg hζ h2 4 0 = 1 := ug88_Bg_mul_Bg hζ h2 (by decide)
  have h3 : ug88_Rg hζ.pow_eq_one 1 2 * ug88_Rg hζ.pow_eq_one 2 1 = 1 :=
    ug88_Rg_mul_Rg hζ.pow_eq_one (by decide)
  have h4 : ug88_Bg hζ h2 0 2 * ug88_Bg hζ h2 2 0 = 1 := ug88_Bg_mul_Bg hζ h2 (by decide)
  unfold ug88_x ug88_y
  calc _ = ug88_Bg hζ h2 0 2 * (ug88_Rg hζ.pow_eq_one 1 2 *
        (ug88_Bg hζ h2 0 4 * ug88_Bg hζ h2 4 0) * ug88_Rg hζ.pow_eq_one 2 1) *
        ug88_Bg hζ h2 2 0 := by simp only [mul_assoc]
    _ = ug88_Bg hζ h2 0 2 * (ug88_Rg hζ.pow_eq_one 1 2 * ug88_Rg hζ.pow_eq_one 2 1) *
        ug88_Bg hζ h2 2 0 := by rw [h1, mul_one]
    _ = ug88_Bg hζ h2 0 2 * ug88_Bg hζ h2 2 0 := by rw [h3, mul_one]
    _ = 1 := h4

theorem ug88_x_val_mul_y {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (h2 : (2 : K) = 0) :
    (ug88_x hζ h2 : Matrix (Fin 5) (Fin 5) K) * (ug88_y hζ h2 : Matrix (Fin 5) (Fin 5) K) = 1 := by
  rw [← Units.val_mul, ug88_x_mul_y hζ h2, Units.val_one]

theorem ug88_x_mulVec {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (h2 : (2 : K) = 0) (v : Fin 5 → K) :
    (ug88_x hζ h2 : Matrix (Fin 5) (Fin 5) K) *ᵥ v =
      ug88_Bm ζ 0 2 *ᵥ (diagonal (ug88_ent ζ 1 2) *ᵥ (ug88_Bm ζ 0 4 *ᵥ v)) := by
  simp only [ug88_x, Units.val_mul, ← mulVec_mulVec]
  rfl

theorem ug88_y_mulVec {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (h2 : (2 : K) = 0) (v : Fin 5 → K) :
    (ug88_y hζ h2 : Matrix (Fin 5) (Fin 5) K) *ᵥ v =
      ug88_Bm ζ 4 0 *ᵥ (diagonal (ug88_ent ζ 2 1) *ᵥ (ug88_Bm ζ 2 0 *ᵥ v)) := by
  simp only [ug88_y, Units.val_mul, ← mulVec_mulVec]
  rfl

theorem ug88_g_mulVec {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (h2 : (2 : K) = 0) (v : Fin 5 → K) :
    (ug88_g hζ h2 : Matrix (Fin 5) (Fin 5) K) *ᵥ v =
      (ug88_x hζ h2 : Matrix (Fin 5) (Fin 5) K) *ᵥ
        (diagonal (ug88_ent ζ 1 2) *ᵥ ((ug88_y hζ h2 : Matrix (Fin 5) (Fin 5) K) *ᵥ v)) := by
  simp only [ug88_g, Units.val_mul, ← mulVec_mulVec]
  rfl

theorem ug88_R_fix {ζ : K} (u : Fin 5 → K) (hu1 : u 1 = 0) (hu2 : u 2 = 0) :
    diagonal (ug88_ent ζ 1 2) *ᵥ u = u := by
  funext k
  fin_cases k <;> simp [ug88_ent, mulVec_diagonal, hu1, hu2]

theorem ug88_R_shift {ζ : K} (u : Fin 5 → K) (hu2 : u 2 = 0) (hu1 : (ζ - 1) * u 1 = 1) :
    diagonal (ug88_ent ζ 1 2) *ᵥ u = u + ![0, 1, 0, 0, 0] := by
  funext k
  fin_cases k
  · simp [ug88_ent, mulVec_diagonal]
  · simp [ug88_ent, mulVec_diagonal]
    linear_combination hu1
  · simp [ug88_ent, mulVec_diagonal, hu2]
  · simp [ug88_ent, mulVec_diagonal]
  · simp [ug88_ent, mulVec_diagonal]

theorem ug88_mulVec_e0 (M : Matrix (Fin 5) (Fin 5) K) (i : Fin 5) :
    (M *ᵥ ![1, 0, 0, 0, 0]) i = M i 0 := by
  simp [mulVec, dotProduct, Fin.sum_univ_five]

theorem ug88_mulVec_e2 (M : Matrix (Fin 5) (Fin 5) K) (i : Fin 5) :
    (M *ᵥ ![0, 0, 1, 0, 0]) i = M i 2 := by
  simp [mulVec, dotProduct, Fin.sum_univ_five]

theorem ug88_add_one_ne {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (h2 : (2 : K) = 0) : ζ + 1 ≠ 0 :=
  fun hc => hζ.ne_one (by norm_num) (by linear_combination hc - h2)

theorem exists_fixer_five_four (h : UnitaryFieldData 2 2 K) {ζ : K} (hζ : IsPrimitiveRoot ζ 5)
    (H : Subgroup (GL (Fin 5) K))
    (hT : ∀ g ∈ unitarySU 2 2 K 5, (∃ t, (g : Matrix (Fin 5) (Fin 5) K) = diagonal t) → g ∈ H)
    (hTw : ∀ g ∈ unitarySU 2 2 K 5, (∃ t, (g : Matrix (Fin 5) (Fin 5) K) * heisFourierMat ζ =
        heisFourierMat ζ * diagonal t) → g ∈ H) :
    ∃ g ∈ H, (∀ i, i ≠ 0 → (g : Matrix (Fin 5) (Fin 5) K) i 0 = 0) ∧
      ¬ IsMonomialMat (g : Matrix (Fin 5) (Fin 5) K) := by
  haveI := h.charP
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hζ5 : ζ ^ 5 = 1 := hζ.pow_eq_one
  have hΦ : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0 := by
    have hs := geom_sum_fin_eq_zero (p := 5) hζ5 (hζ.ne_one (by norm_num))
    norm_num [Fin.sum_univ_five] at hs
    linear_combination hs
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  have hRmem : ∀ i j : Fin 5, i ≠ j → ug88_Rg hζ5 i j ∈ H := fun i j hij =>
    hT _ (ug88_diagGL_mem h (ug88_ent_pow hζ5 i j) (ug88_ent_prod hζ5 hij)) ⟨ug88_ent ζ i j, rfl⟩
  have hBmem : ∀ i j : Fin 5, i ≠ j → ug88_Bg hζ h2 i j ∈ H := fun i j hij =>
    hTw _ (ug88_conjGL_mem h hζ h2 (ug88_ent_pow hζ5 i j) (ug88_ent_prod hζ5 hij))
      ⟨ug88_ent ζ i j, ug88_conjGL_tw hζ h2 (ug88_ent_pow hζ5 i j)⟩
  have hx : ug88_x hζ h2 ∈ H :=
    H.mul_mem (H.mul_mem (hBmem 0 2 (by decide)) (hRmem 1 2 (by decide))) (hBmem 0 4 (by decide))
  have hy : ug88_y hζ h2 ∈ H :=
    H.mul_mem (H.mul_mem (hBmem 4 0 (by decide)) (hRmem 2 1 (by decide))) (hBmem 2 0 (by decide))
  have hg : ug88_g hζ h2 ∈ H := H.mul_mem (H.mul_mem hx (hRmem 1 2 (by decide))) hy
  have hY0 : (ug88_y hζ h2 : Matrix (Fin 5) (Fin 5) K) *ᵥ ![1, 0, 0, 0, 0] =
      ug88_Bm ζ 4 0 *ᵥ (diagonal (ug88_ent ζ 2 1) *ᵥ ug88_w1 ζ) := by
    rw [ug88_y_mulVec, ug88_stage1 hζ h2 hΦ]
  have hY2 : (ug88_y hζ h2 : Matrix (Fin 5) (Fin 5) K) *ᵥ ![0, 0, 1, 0, 0] =
      ug88_Bm ζ 4 0 *ᵥ (diagonal (ug88_ent ζ 2 1) *ᵥ ug88_w2 ζ) := by
    rw [ug88_y_mulVec, ug88_stage2 hζ h2 hΦ]
  have hX1 : (ug88_x hζ h2 : Matrix (Fin 5) (Fin 5) K) *ᵥ ![0, 1, 0, 0, 0] =
      ug88_Bm ζ 0 2 *ᵥ (diagonal (ug88_ent ζ 1 2) *ᵥ ug88_w3 ζ) := by
    rw [ug88_x_mulVec, ug88_stage3 hζ h2 hΦ]
  have hu1 : ((ug88_y hζ h2 : Matrix (Fin 5) (Fin 5) K) *ᵥ ![1, 0, 0, 0, 0]) 1 = 0 := by
    rw [hY0]
    exact ug88_final_Y0_1 hζ h2 hΦ
  have hu2 : ((ug88_y hζ h2 : Matrix (Fin 5) (Fin 5) K) *ᵥ ![1, 0, 0, 0, 0]) 2 = 0 := by
    rw [hY0]
    exact ug88_final_Y0_2 hζ h2 hΦ
  have hv2 : ((ug88_y hζ h2 : Matrix (Fin 5) (Fin 5) K) *ᵥ ![0, 0, 1, 0, 0]) 2 = 0 := by
    rw [hY2]
    exact ug88_final_Y2_2 hζ h2 hΦ
  have hv1 : (ζ - 1) * ((ug88_y hζ h2 : Matrix (Fin 5) (Fin 5) K) *ᵥ ![0, 0, 1, 0, 0]) 1 = 1 := by
    rw [hY2]
    exact ug88_final_Y2_1 hζ h2 hΦ
  have hx1 : ((ug88_x hζ h2 : Matrix (Fin 5) (Fin 5) K) *ᵥ ![0, 1, 0, 0, 0]) 1 = (ζ + 1) ^ 3 := by
    rw [hX1]
    exact ug88_final_X1_1 hζ h2 hΦ
  have hx3 : ((ug88_x hζ h2 : Matrix (Fin 5) (Fin 5) K) *ᵥ ![0, 1, 0, 0, 0]) 3 = ζ := by
    rw [hX1]
    exact ug88_final_X1_3 hζ h2 hΦ
  have hg0 : (ug88_g hζ h2 : Matrix (Fin 5) (Fin 5) K) *ᵥ ![1, 0, 0, 0, 0] =
      ![1, 0, 0, 0, 0] := by
    rw [ug88_g_mulVec, ug88_R_fix _ hu1 hu2, mulVec_mulVec, ug88_x_val_mul_y, one_mulVec]
  have hg2 : (ug88_g hζ h2 : Matrix (Fin 5) (Fin 5) K) *ᵥ ![0, 0, 1, 0, 0] =
      ![0, 0, 1, 0, 0] + (ug88_x hζ h2 : Matrix (Fin 5) (Fin 5) K) *ᵥ ![0, 1, 0, 0, 0] := by
    rw [ug88_g_mulVec, ug88_R_shift _ hv2 hv1, mulVec_add, mulVec_mulVec, ug88_x_val_mul_y,
      one_mulVec]
  have hcol0 : ∀ i : Fin 5, i ≠ 0 → (ug88_g hζ h2 : Matrix (Fin 5) (Fin 5) K) i 0 = 0 := by
    intro i hi
    have h := congrFun hg0 i
    rw [ug88_mulVec_e0] at h
    rw [h]
    fin_cases i <;> first | exact absurd rfl hi | simp
  have hg12 : (ug88_g hζ h2 : Matrix (Fin 5) (Fin 5) K) 1 2 = (ζ + 1) ^ 3 := by
    have h := congrFun hg2 1
    rw [ug88_mulVec_e2, Pi.add_apply, hx1] at h
    rw [h]
    simp
  have hg32 : (ug88_g hζ h2 : Matrix (Fin 5) (Fin 5) K) 3 2 = ζ := by
    have h := congrFun hg2 3
    rw [ug88_mulVec_e2, Pi.add_apply, hx3] at h
    rw [h]
    simp
  have hmono : ¬ IsMonomialMat (ug88_g hζ h2 : Matrix (Fin 5) (Fin 5) K) := by
    intro hm
    have h12 : (ug88_g hζ h2 : Matrix (Fin 5) (Fin 5) K) 1 2 ≠ 0 := by
      rw [hg12]
      exact pow_ne_zero 3 (ug88_add_one_ne hζ h2)
    have h32 : (ug88_g hζ h2 : Matrix (Fin 5) (Fin 5) K) 3 2 ≠ 0 := by
      rw [hg32]
      exact hζ0
    exact absurd (hm 2 1 3 h12 h32) (by decide)
  exact ⟨ug88_g hζ h2, hg, hcol0, hmono⟩

end CFSG.LieType.SeitzGeneration

end
