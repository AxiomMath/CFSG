module

public import CFSG.ClassicalInvolution.Asc77.AscCX9Z7
public import CFSG.ClassicalInvolution.Asc77.AscCX9X3
public import CFSG.ClassicalInvolution.Asc77.AscCX9Z4

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX.MF2U

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
  CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.Asc77.CX.MF2L (kappa_longBlock0 uT twGL coe_twGL coe_twGL_inv)
open CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4 (blockMat_four_zero)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)
open scoped MatrixGroups

section Matrices

variable {K : Type} [Field K] {σ : K ≃+* K}

theorem d0_descH {c t m n : K} (hc : c ≠ 0) (ht : t ≠ 0) (hσt : σ t = -t) :
    diagonal ![-1, 1, 1, 1] * descH σ c t m n =
      descH σ c t m n * blockMat 4 0 !![0, -t; -t⁻¹, 0] := by
  rw [blockMat_four_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [descH, hσt, Matrix.mul_apply, Fin.sum_univ_four] <;>
    field_simp

theorem map_blockMat {L : Type} [Field L] (φ : L →+* K) {i k : ℕ}
    (A : Matrix (Fin k) (Fin k) L) : (blockMat 4 i A).map φ = blockMat 4 i (A.map φ) := by
  ext a b
  rw [Matrix.map_apply, blockMat_apply, blockMat_apply]
  split_ifs
  · rfl
  · rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

theorem conj_transport {H Hi P d L₁ L₂ : Matrix (Fin 4) (Fin 4) K} (hH : Hi * H = 1)
    (hd : d * d = 1) (hdH : d * H = H * P) (h : d * (H * L₁ * Hi) * d = H * L₂ * Hi) :
    P * L₁ = L₂ * P := by
  have e1 : d * (H * L₁ * Hi) * d * (d * H) = H * (P * L₁) := by
    calc d * (H * L₁ * Hi) * d * (d * H) = d * H * L₁ * Hi * (d * d) * H := by
          simp only [Matrix.mul_assoc]
      _ = d * H * L₁ * (Hi * H) := by
          rw [hd, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = H * (P * L₁) := by rw [hH, Matrix.mul_one, hdH, Matrix.mul_assoc]
  have e2 : H * L₂ * Hi * (d * H) = H * (L₂ * P) := by
    rw [hdH]
    calc H * L₂ * Hi * (H * P) = H * L₂ * (Hi * H) * P := by simp only [Matrix.mul_assoc]
      _ = H * (L₂ * P) := by rw [hH, Matrix.mul_one, Matrix.mul_assoc]
  rw [h, e2] at e1
  calc P * L₁ = Hi * H * (P * L₁) := by rw [hH, Matrix.one_mul]
    _ = Hi * H * (L₂ * P) := by rw [Matrix.mul_assoc, ← e1, ← Matrix.mul_assoc]
    _ = L₂ * P := by rw [hH, Matrix.one_mul]

end Matrices

theorem isSquare_det_of_comm {L : Type} [Field L] {N : Matrix (Fin 2) (Fin 2) L}
    (h : N * !![1, -1; 0, 1] = !![1, -1; 0, 1] * N) : IsSquare N.det := by
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
  refine ⟨N 0 0, ?_⟩
  rw [Matrix.det_fin_two]
  have e11 : N 1 1 = N 0 0 := by linear_combination h01
  rw [h00, e11]
  ring

theorem tw_uT {L : Type} [Field L] :
    ((slConjugation 2 L (twGL (one_ne_zero (α := L))) (uT 1) : SL(2, L)) :
      Matrix (Fin 2) (Fin 2) L) = !![1, -1; 0, 1] := by
  rw [slConjugation_matrix, coe_twGL_inv, coe_twGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uT, Matrix.mul_diagonal, Matrix.diagonal_mul]

namespace DescData

variable {K : Type} [Field K] {σ : K ≃+* K} {F : Type} [Field F] (D : DescData σ F)

theorem suMat_kU_longBlock0 (b : SL(2, F)) :
    suMat (D.kU (longBlock F 2 0 b)) = descH σ D.c D.t D.m D.n *
      blockMat 4 0 (((slConjugation 2 F (twGL (one_ne_zero (α := F))) b : SL(2, F)) :
        Matrix (Fin 2) (Fin 2) F).map D.ι) * descHInv σ D.c D.t D.m D.n := by
  rw [suMat_kU, kap1, kappa_longBlock0, WeakCT.coe_blockSL, map_blockMat]

theorem d0_kU_ne (hσt : σ D.t = -D.t) (h2 : (2 : K) ≠ 0) (hsq : IsSquare (-1 : F))
    (b : SL(2, F)) :
    d0SU (D.kU (longBlock F 2 0 (uT 1))) ≠ D.kU (longBlock F 2 0 (b * uT 1 * b⁻¹)) := by
  intro h
  have ht0 : D.t ≠ 0 := fun h0 => D.ht (by rw [h0, map_zero, sub_zero])
  set e := slConjugation 2 F (twGL (one_ne_zero (α := F))) with he
  have h1 := congrArg suMat h
  rw [suMat_d0SU, suMat_kU_longBlock0, suMat_kU_longBlock0] at h1
  have h3 := conj_transport (descHInv_mul D.hc D.ht D.hm D.hn) d0_mul_d0
    (d0_descH D.hc ht0 hσt) h1
  rw [← blockMat_mul (by norm_num : 0 + 2 ≤ 4), ← blockMat_mul (by norm_num : 0 + 2 ≤ 4)] at h3
  have h4 := blockMat_injective (by norm_num : 0 + 2 ≤ 4) h3
  obtain ⟨τ, hτ⟩ := D.onto (D.t ^ 2) (by rw [map_pow, hσt, neg_sq])
  set w₀ : Matrix (Fin 2) (Fin 2) F := !![0, -τ; -1, 0] with hw₀
  have hw : (w₀.map D.ι) = D.t • !![0, -D.t; -D.t⁻¹, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hw₀, hτ, ht0, sq]
  have hu : ((e (uT 1) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, -1; 0, 1] := tw_uT
  have hb : ((e (b * uT 1 * b⁻¹) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      (e b : Matrix (Fin 2) (Fin 2) F) * !![1, -1; 0, 1] *
        (((e b)⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
    rw [map_mul, map_mul, map_inv, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, hu]
  rw [hu, hb] at h4
  have h5 : (w₀ * !![1, -1; 0, 1]).map D.ι =
      ((e b : Matrix (Fin 2) (Fin 2) F) * !![1, -1; 0, 1] *
        (((e b)⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * w₀).map D.ι := by
    rw [Matrix.map_mul, Matrix.map_mul, hw, Matrix.smul_mul, Matrix.mul_smul, h4]
  have h6 := Matrix.map_injective D.ι.injective h5
  set B : Matrix (Fin 2) (Fin 2) F := (e b : Matrix (Fin 2) (Fin 2) F) with hB
  set Bi : Matrix (Fin 2) (Fin 2) F := (((e b)⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)
    with hBi
  have hBB : Bi * B = 1 := by
    rw [hB, hBi, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have h7 : (Bi * w₀) * !![1, -1; 0, 1] = !![1, -1; 0, 1] * (Bi * w₀) := by
    calc (Bi * w₀) * !![1, -1; 0, 1] = Bi * (B * !![1, -1; 0, 1] * Bi * w₀) := by
          rw [Matrix.mul_assoc, ← h6]
      _ = (Bi * B) * !![1, -1; 0, 1] * (Bi * w₀) := by simp only [Matrix.mul_assoc]
      _ = !![1, -1; 0, 1] * (Bi * w₀) := by rw [hBB, Matrix.one_mul]
  obtain ⟨r, hr⟩ := isSquare_det_of_comm h7
  have hdetBi : Bi.det = 1 := ((e b)⁻¹ : SL(2, F)).2
  rw [det_mul, hdetBi, one_mul, hw₀, Matrix.det_fin_two_of] at hr
  obtain ⟨ω, hω⟩ := hsq
  have hτ' : τ = (ω * r) * (ω * r) := by linear_combination -hr + r ^ 2 * hω
  have ht2 : D.t ^ 2 = D.ι (ω * r) * D.ι (ω * r) := by rw [← hτ, hτ', map_mul]
  have h8 : (D.t - D.ι (ω * r)) * (D.t + D.ι (ω * r)) = 0 := by linear_combination ht2
  have hfix := D.fix (ω * r)
  rcases mul_eq_zero.mp h8 with h9 | h9
  · have e1 : D.t = D.ι (ω * r) := by linear_combination h9
    have : σ D.t = D.t := by rw [e1, hfix]
    exact ht0 (by
      have h10 : (2 : K) * D.t = 0 := by linear_combination hσt - this
      exact (mul_eq_zero.mp h10).resolve_left h2)
  · have e1 : D.t = -D.ι (ω * r) := by linear_combination h9
    have : σ D.t = D.t := by rw [e1, map_neg, hfix]
    exact ht0 (by
      have h10 : (2 : K) * D.t = 0 := by linear_combination hσt - this
      exact (mul_eq_zero.mp h10).resolve_left h2)

end DescData

end CFSG.ClassicalInvolution.Asc77.CX.MF2U
