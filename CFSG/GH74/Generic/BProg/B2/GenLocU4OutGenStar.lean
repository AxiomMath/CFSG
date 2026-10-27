module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutGenSplit

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace GenLocU4Out

open GenLocU4Basic

variable {K : Type} [Field K] {p f : ℕ}

@[expose] def rot12 : Matrix (Fin 4) (Fin 4) K := !![1, 0, 0, 0; 0, 0, 1, 0; 0, -1, 0, 0; 0, 0, 0, 1]

@[expose] def quarter23 : Matrix (Fin 4) (Fin 4) K := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0]

@[expose] def piMat : Matrix (Fin 4) (Fin 4) K := !![0, 0, 1, 0; 0, 0, 0, 1; -1, 0, 0, 0; 0, -1, 0, 0]

theorem rot12_det : (rot12 : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  simp [rot12, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem quarter23_det : (quarter23 : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  simp [quarter23, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem rot12_map (hq : Odd (p ^ f)) : (rot12 : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)) = rot12 := by
  have hq0 : p ^ f ≠ 0 := hq.pos.ne'
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rot12, zero_pow hq0, Odd.neg_pow hq]

theorem quarter23_map (hq : Odd (p ^ f)) :
    (quarter23 : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)) = quarter23 := by
  have hq0 : p ^ f ≠ 0 := hq.pos.ne'
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quarter23, zero_pow hq0, Odd.neg_pow hq]

theorem rot12_unitary (hq : Odd (p ^ f)) : IsUnitaryU (p ^ f) (rot12 : Matrix (Fin 4) (Fin 4) K) := by
  unfold IsUnitaryU
  rw [rot12_map hq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rot12, Matrix.mul_apply, Fin.sum_univ_four]

theorem quarter23_unitary (hq : Odd (p ^ f)) :
    IsUnitaryU (p ^ f) (quarter23 : Matrix (Fin 4) (Fin 4) K) := by
  unfold IsUnitaryU
  rw [quarter23_map hq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quarter23, Matrix.mul_apply, Fin.sum_univ_four]

theorem rot12_fixOut (δ : K) (hq : Odd (p ^ f)) :
    FixOut (p ^ f) (Matrix.diagonal ![1, 1, 1, δ] : Matrix (Fin 4) (Fin 4) K)
      (suOf (p ^ f) rot12 (rot12_unitary hq) rot12_det) := by
  unfold FixOut
  rw [coe_suOf, rot12_map hq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rot12, Matrix.mul_apply, Matrix.diagonal]

theorem quarter23_inBlock (hq : Odd (p ^ f)) :
    GenLocU4Gen.InBlock (p ^ f) (1 : GL (Fin 4) K) 2
      (suOf (p ^ f) quarter23 (quarter23_unitary hq) quarter23_det) := by
  refine ⟨!![0, 1; -1, 0], ?_, ?_, ?_⟩
  · simp [Matrix.det_fin_two_of]
  · have hq0 : p ^ f ≠ 0 := hq.pos.ne'
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, zero_pow hq0, Odd.neg_pow hq]
  · simp only [inv_one, one_mul, mul_one]
    rw [coe_suOf]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [quarter23, CFSG.ClassicalInvolution.Phan.blockMat_apply]

theorem rot12_transpose : (rot12 : Matrix (Fin 4) (Fin 4) K)ᵀ = !![1, 0, 0, 0; 0, 0, -1, 0; 0, 1, 0, 0; 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rot12, Matrix.transpose_apply]

theorem piMat_eq :
    (rot12 : Matrix (Fin 4) (Fin 4) K) * quarter23 * (rot12 : Matrix (Fin 4) (Fin 4) K)ᵀ * rot02 = piMat := by
  rw [rot12_transpose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot12, quarter23, rot02, piMat, Matrix.mul_apply, Fin.sum_univ_four]

theorem piMat_transpose_mul : (piMat : Matrix (Fin 4) (Fin 4) K)ᵀ * piMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [piMat, Matrix.mul_apply, Fin.sum_univ_four]

theorem conj_block0_to_block2 (B : Matrix (Fin 2) (Fin 2) K) :
    (piMat : Matrix (Fin 4) (Fin 4) K)ᵀ * CFSG.ClassicalInvolution.Phan.blockMat 4 0 B * piMat =
      CFSG.ClassicalInvolution.Phan.blockMat 4 2 B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [piMat, CFSG.ClassicalInvolution.Phan.blockMat_apply, Matrix.mul_apply, Fin.sum_univ_four]

theorem eq_top_of_SO_star [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    (_hq : p ^ f % 4 = 1) (Γ : Subgroup ↥(StatedSU 4 (p ^ f) K)) (δ : K) (_hδ : δ ^ (p ^ f + 1) = 1)
    (_hδs : ∀ μ : K, μ ^ (p ^ f + 1) = 1 → μ * μ ≠ δ)
    (hSO : ∀ g : ↥(StatedSU 4 (p ^ f) K),
      Matrix.diagonal ![1, 1, 1, δ] * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)) =
        ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * Matrix.diagonal ![1, 1, 1, δ] → g ∈ Γ)
    (h23 : ∀ g, GenLocU4Gen.InBlock (p ^ f) (1 : GL (Fin 4) K) 2 g → g ∈ Γ) : Γ = ⊤ := by
  have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  let rG02 : ↥(StatedSU 4 (p ^ f) K) := suOf (p ^ f) rot02 (rot02_unitary hq) rot02_det
  let rG12 : ↥(StatedSU 4 (p ^ f) K) := suOf (p ^ f) rot12 (rot12_unitary hq) rot12_det
  let qG : ↥(StatedSU 4 (p ^ f) K) := suOf (p ^ f) quarter23 (quarter23_unitary hq) quarter23_det
  have h02 : rG02 ∈ Γ := hSO _ (rot02_fixOut δ hq)
  have h12 : rG12 ∈ Γ := hSO _ (rot12_fixOut δ hq)
  have hqΓ : qG ∈ Γ := h23 _ (quarter23_inBlock hq)
  let πG : ↥(StatedSU 4 (p ^ f) K) := rG12 * qG * rG12⁻¹ * rG02
  have hπ : πG ∈ Γ := Γ.mul_mem (Γ.mul_mem (Γ.mul_mem h12 hqΓ) (Γ.inv_mem h12)) h02
  have hπmat : ((πG : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = piMat := by
    have e : ((πG : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        rot12 * quarter23 * ((rot12 : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * rot02 := by
      simp only [πG, rG12, qG, rG02, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
      rw [coe_inv_suOf]
      rfl
    rw [e, rot12_map hq]
    exact piMat_eq
  have hπinv : (((πG : GL (Fin 4) K)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = (piMat : Matrix (Fin 4) (Fin 4) K)ᵀ :=
    Units.inv_eq_of_mul_eq_one_left (by rw [hπmat]; exact piMat_transpose_mul)
  have hB0 : ∀ g, GenLocU4Gen.InBlock (p ^ f) (1 : GL (Fin 4) K) 0 g → g ∈ Γ := by
    rintro g ⟨B, hdet, hunit, hg⟩
    have hg1 : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        CFSG.ClassicalInvolution.Phan.blockMat 4 0 B := by simpa using hg
    have hg' : GenLocU4Gen.InBlock (p ^ f) (1 : GL (Fin 4) K) 2 (πG⁻¹ * g * πG) := by
      refine ⟨B, hdet, hunit, ?_⟩
      simp only [inv_one, one_mul, mul_one, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, hπinv, hπmat, hg1]
      exact conj_block0_to_block2 B
    have h1 : πG⁻¹ * g * πG ∈ Γ := h23 _ hg'
    have h2 : g = πG * (πG⁻¹ * g * πG) * πG⁻¹ := by group
    rw [h2]
    exact Γ.mul_mem (Γ.mul_mem hπ h1) (Γ.inv_mem hπ)
  exact eq_top_of_blocks_rot hp hp2 hK Γ δ hSO hB0 h23

end GenLocU4Out

end CFSG.GH74.Generic.BProg.B2
