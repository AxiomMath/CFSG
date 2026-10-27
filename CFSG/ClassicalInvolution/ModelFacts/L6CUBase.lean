module

public import CFSG.ClassicalInvolution.ModelFacts.L6CMat
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutMain
public import CFSG.LinearAlgebra.LinearGroups.UnitaryFourOrder

public section

namespace CFSG.ClassicalInvolution.ModelFacts.L6C

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open scoped MatrixGroups

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

local notation "𝕄₄" => Matrix (Fin 4) (Fin 4) K

@[expose] noncomputable def uadj {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) K :=
  (M.map h.bar)ᵀ

theorem uadj_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    uadj h M i j = h.bar (M j i) := rfl

theorem uadj_mul {n : ℕ} (M N : Matrix (Fin n) (Fin n) K) :
    uadj h (M * N) = uadj h N * uadj h M := by
  simp only [uadj, Matrix.map_mul, Matrix.transpose_mul]

theorem uadj_one {n : ℕ} : uadj h (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  simp [uadj]

theorem map_bar_bar {n : ℕ} (M : Matrix (Fin n) (Fin n) K) : (M.map h.bar).map h.bar = M := by
  ext i j
  simp [h.bar_bar]

theorem map_bar_uadj {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    (uadj h M).map h.bar = Mᵀ := by
  rw [uadj, Matrix.transpose_map, map_bar_bar]

theorem uadj_smul {n : ℕ} (c : K) (M : Matrix (Fin n) (Fin n) K) :
    uadj h (c • M) = h.bar c • uadj h M := by
  ext i j
  simp [uadj]

theorem map_bar_rot4 : (rot4 K : 𝕄₄).map h.bar = (rot4 K : 𝕄₄) := by
  rw [coe_rot4]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem uadj_rot4_mul : uadj h (rot4 K : 𝕄₄) * (rot4 K : 𝕄₄) = 1 := by
  rw [uadj, coe_rot4]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem commutes_rot4_of_entries (N : 𝕄₄) (h00 : N 0 0 = N 1 1) (h01 : N 0 1 = -N 1 0)
    (h02 : N 0 2 = 0) (h03 : N 0 3 = 0) (h12 : N 1 2 = 0) (h13 : N 1 3 = 0) (h20 : N 2 0 = 0)
    (h21 : N 2 1 = 0) (h30 : N 3 0 = 0) (h31 : N 3 1 = 0) :
    N * (rot4 K : 𝕄₄) = (rot4 K : 𝕄₄) * N := by
  rw [coe_rot4]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, h00, h01, h02, h03, h12, h13, h20, h21, h30, h31]

theorem comm_of_frame {Q M N : 𝕄₄} (hQ : uadj h Q * Q = 1) (hN : N = uadj h Q * M * Q)
    (hNr : N * (rot4 K : 𝕄₄) = (rot4 K : 𝕄₄) * N) :
    M * (Q * (rot4 K : 𝕄₄) * uadj h Q) = Q * (rot4 K : 𝕄₄) * uadj h Q * M := by
  have hQQ : Q * uadj h Q = 1 := mul_eq_one_comm.mp hQ
  have hMQ : M * Q = Q * N := by
    rw [hN]
    calc M * Q = (Q * uadj h Q) * M * Q := by rw [hQQ, Matrix.one_mul]
      _ = Q * (uadj h Q * M * Q) := by simp only [Matrix.mul_assoc]
  exact MF15.conj_comm_matrix hQQ hQ hMQ hNr

theorem semicomm_of_frame {Q M N : 𝕄₄} (hQ : uadj h Q * Q = 1)
    (hN : N = uadj h Q * M * Q.map h.bar) (hNr : N * (rot4 K : 𝕄₄) = (rot4 K : 𝕄₄) * N) :
    M * ((Q * (rot4 K : 𝕄₄) * uadj h Q).map h.bar) = Q * (rot4 K : 𝕄₄) * uadj h Q * M := by
  have hQQ : Q * uadj h Q = 1 := mul_eq_one_comm.mp hQ
  have hbb : Q.map h.bar * Qᵀ = 1 := by
    have := congrArg (fun X : 𝕄₄ => X.map h.bar) hQQ
    simpa [Matrix.map_mul, map_bar_uadj, Matrix.map_one _ (map_zero h.bar) (map_one h.bar)]
      using this
  have e1 : (Q * (rot4 K : 𝕄₄) * uadj h Q).map h.bar = Q.map h.bar * (rot4 K : 𝕄₄) * Qᵀ := by
    rw [Matrix.map_mul, Matrix.map_mul, map_bar_rot4 h, map_bar_uadj]
  have hMQ : M * Q.map h.bar = Q * N := by
    rw [hN]
    calc M * Q.map h.bar = (Q * uadj h Q) * M * Q.map h.bar := by rw [hQQ, Matrix.one_mul]
      _ = Q * (uadj h Q * M * Q.map h.bar) := by simp only [Matrix.mul_assoc]
  have hNQ : N * Qᵀ = uadj h Q * M := by
    rw [hN]
    calc uadj h Q * M * Q.map h.bar * Qᵀ = uadj h Q * M * (Q.map h.bar * Qᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = uadj h Q * M := by rw [hbb, Matrix.mul_one]
  rw [e1]
  calc M * (Q.map h.bar * (rot4 K : 𝕄₄) * Qᵀ)
      = (M * Q.map h.bar) * (rot4 K : 𝕄₄) * Qᵀ := by simp only [Matrix.mul_assoc]
    _ = Q * (N * (rot4 K : 𝕄₄)) * Qᵀ := by rw [hMQ]; simp only [Matrix.mul_assoc]
    _ = Q * ((rot4 K : 𝕄₄) * N) * Qᵀ := by rw [hNr]
    _ = Q * (rot4 K : 𝕄₄) * (N * Qᵀ) := by simp only [Matrix.mul_assoc]
    _ = Q * (rot4 K : 𝕄₄) * uadj h Q * M := by rw [hNQ]; simp only [Matrix.mul_assoc]

@[expose] noncomputable def rotSU4 : unitarySU p f K 4 :=
  ⟨Matrix.SpecialLinearGroup.toGL (rot4 K), (mem_unitarySU_iff h).mpr
    ⟨by simp, by simpa [uadj] using uadj_rot4_mul h⟩⟩

theorem coe_rotSU4 :
    ((rotSU4 h : unitarySU p f K 4) : GL (Fin 4) K) =
      ((rot4 K : SL(4, K)) : GL (Fin 4) K) := rfl

theorem coe_inv_unitarySU4 (k : unitarySU p f K 4) :
    (((k⁻¹ : unitarySU p f K 4) : GL (Fin 4) K) : 𝕄₄) = uadj h ((k : GL (Fin 4) K) : 𝕄₄) := by
  have hk := ((mem_unitarySU_iff h).mp k.2).2
  have h1 : (((k⁻¹ : unitarySU p f K 4) : GL (Fin 4) K) : 𝕄₄) =
      uadj h ((k : GL (Fin 4) K) : 𝕄₄) * (((k : GL (Fin 4) K) : 𝕄₄) *
        (((k⁻¹ : unitarySU p f K 4) : GL (Fin 4) K) : 𝕄₄)) := by
    rw [← Matrix.mul_assoc, show uadj h ((k : GL (Fin 4) K) : 𝕄₄) * ((k : GL (Fin 4) K) : 𝕄₄) = 1
      from hk, Matrix.one_mul]
  have h2 : ((k : GL (Fin 4) K) : 𝕄₄) * (((k⁻¹ : unitarySU p f K 4) : GL (Fin 4) K) : 𝕄₄) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]
    rfl
  rw [h1, h2, Matrix.mul_one]

theorem coe_conj_rotSU4 (k : unitarySU p f K 4) :
    ((k * rotSU4 h * k⁻¹ : unitarySU p f K 4) : GL (Fin 4) K).val =
      ((k : GL (Fin 4) K) : 𝕄₄) * (rot4 K : 𝕄₄) * uadj h ((k : GL (Fin 4) K) : 𝕄₄) := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_inv_unitarySU4 h]
  rfl

variable [Finite K]

theorem exists_unitarySU_of_unitary4 {Q : 𝕄₄} (hQ : uadj h Q * Q = 1) :
    ∃ k : unitarySU p f K 4,
      ((k : GL (Fin 4) K) : 𝕄₄) * (rot4 K : 𝕄₄) * uadj h ((k : GL (Fin 4) K) : 𝕄₄) =
        Q * (rot4 K : 𝕄₄) * uadj h Q := by
  have hd : h.bar Q.det * Q.det = 1 := by
    have := congrArg Matrix.det hQ
    rw [det_mul, det_one] at this
    have e : (uadj h Q).det = h.bar Q.det := by
      rw [uadj, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rwa [e] at this
  have hd0 : Q.det ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at hd
    exact zero_ne_one hd
  obtain ⟨D, hD⟩ : ∃ D : 𝕄₄, D = Matrix.diagonal ![1, 1, 1, Q.det⁻¹] := ⟨_, rfl⟩
  have hadjD : uadj h D = Matrix.diagonal ![1, 1, 1, h.bar Q.det⁻¹] := by
    rw [hD, uadj, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]
    congr 1
    funext i
    fin_cases i <;> simp
  have hDD : uadj h D * D = 1 := by
    rw [hadjD, hD, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i
    · simp
    · simp
    · simp
    · simp only [Fin.reduceFinMk, Matrix.cons_val]
      rw [map_inv₀, ← mul_inv, hd, inv_one]
  have hDD' : D * uadj h D = 1 := mul_eq_one_comm.mp hDD
  set Km : 𝕄₄ := Q * D with hKm
  have hKdet : Km.det = 1 := by
    rw [hKm, det_mul, hD, det_diagonal]
    simp [Fin.prod_univ_four, hd0]
  have hKK : uadj h Km * Km = 1 := by
    calc uadj h Km * Km = uadj h D * (uadj h Q * Q) * D := by
          rw [hKm, uadj_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQ, Matrix.mul_one, hDD]
  let kgl : GL (Fin 4) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero Km (by rw [hKdet]; exact one_ne_zero)
  have hkgl : (kgl : 𝕄₄) = Km := rfl
  have hmem : kgl ∈ unitarySU p f K 4 := (mem_unitarySU_iff h).mpr ⟨by rw [hkgl]; exact hKdet,
    by rw [hkgl]; exact hKK⟩
  refine ⟨⟨kgl, hmem⟩, ?_⟩
  show Km * (rot4 K : 𝕄₄) * uadj h Km = _
  have hRD : D * (rot4 K : 𝕄₄) = (rot4 K : 𝕄₄) * D := by
    rw [hD]; exact diagonal_mul_rot4 (by simp)
  calc Km * (rot4 K : 𝕄₄) * uadj h Km = Q * (D * (rot4 K : 𝕄₄)) * (uadj h D * uadj h Q) := by
        rw [hKm, uadj_mul]; simp only [Matrix.mul_assoc]
    _ = Q * (rot4 K : 𝕄₄) * (D * uadj h D) * uadj h Q := by
        rw [hRD]; simp only [Matrix.mul_assoc]
    _ = Q * (rot4 K : 𝕄₄) * uadj h Q := by rw [hDD', Matrix.mul_one]

end CFSG.ClassicalInvolution.ModelFacts.L6C
