module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4HBlocks

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace HBlocks

open Matrix CFSG.LocalAnalysis.ComponentInitial UnitaryOut UnitaryConj

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] def ul (M : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin 2) (Fin 2) K :=
  !![M 0 0, M 0 1; M 1 0, M 1 1]

@[expose] def IsBD (M : Matrix (Fin 4) (Fin 4) K) : Prop :=
  M 0 2 = 0 ∧ M 0 3 = 0 ∧ M 1 2 = 0 ∧ M 1 3 = 0 ∧ M 2 0 = 0 ∧ M 2 1 = 0 ∧ M 3 0 = 0 ∧
    M 3 1 = 0

theorem isBD_of_comm_X1 (h2 : (2 : K) ≠ 0) {l : K} (hl : l ≠ 0) {M : Matrix (Fin 4) (Fin 4) K}
    (hM : M * X1 l = X1 l * M) : IsBD M := by
  have h2l : (2 * l) ≠ 0 := mul_ne_zero h2 hl
  have key : ∀ i j : Fin 4, (M * X1 l) i j = (X1 l * M) i j := fun i j => by rw [hM]
  have e : ∀ (i j : Fin 4) (c : K), c ≠ 0 → M i j * c = 0 → M i j = 0 := fun i j c hc hm =>
    (mul_eq_zero.1 hm).resolve_right hc
  have hneg : -(2 * l) ≠ 0 := neg_ne_zero.2 h2l
  refine ⟨e 0 2 (-(2 * l)) hneg ?_, e 0 3 (-(2 * l)) hneg ?_, e 1 2 (-(2 * l)) hneg ?_,
    e 1 3 (-(2 * l)) hneg ?_, e 2 0 (2 * l) h2l ?_, e 2 1 (2 * l) h2l ?_, e 3 0 (2 * l) h2l ?_,
    e 3 1 (2 * l) h2l ?_⟩ <;>
  [have k := key 0 2; have k := key 0 3; have k := key 1 2; have k := key 1 3;
    have k := key 2 0; have k := key 2 1; have k := key 3 0; have k := key 3 1] <;>
  simp only [X1, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.cons_val, mul_zero, zero_mul, add_zero, zero_add] at k <;>
  linear_combination k

theorem ul_mul {M N : Matrix (Fin 4) (Fin 4) K} (hM : IsBD M) (hN : IsBD N) :
    ul (M * N) = ul M * ul N := by
  obtain ⟨m02, m03, m12, m13, -, -, -, -⟩ := hM
  obtain ⟨-, -, -, -, n20, n21, n30, n31⟩ := hN
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ul, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, m02, m03, m12, m13, n20, n21,
      n30, n31]

theorem ul_one : ul (1 : Matrix (Fin 4) (Fin 4) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ul]

theorem eq_one_of_ul_eq_one {M : Matrix (Fin 4) (Fin 4) K} (hM : IsBD M)
    (hU : uStar h M * stdG * M = stdG) (h1 : ul M = 1) : M = 1 := by
  obtain ⟨m02, m03, m12, m13, m20, m21, m30, m31⟩ := hM
  have u00 : M 0 0 = 1 := by simpa [ul] using congrFun (congrFun h1 0) 0
  have u01 : M 0 1 = 0 := by simpa [ul] using congrFun (congrFun h1 0) 1
  have u10 : M 1 0 = 0 := by simpa [ul] using congrFun (congrFun h1 1) 0
  have u11 : M 1 1 = 1 := by simpa [ul] using congrFun (congrFun h1 1) 1
  have e02 := congrFun (congrFun hU 0) 2
  have e03 := congrFun (congrFun hU 0) 3
  have e12 := congrFun (congrFun hU 1) 2
  have e13 := congrFun (congrFun hU 1) 3
  simp [uStar, stdG, Matrix.mul_apply, Fin.sum_univ_four, m02, m03, m12, m13, m20, m21, m30, m31,
    u00, u01, u10, u11] at e02 e03 e12 e13
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m02, m03, m12, m13, m20, m21, m30, m31, u00, u01, u10, u11, e02, e03, e12, e13]

theorem Hd_comm_U12 {d : K} (hd : d ≠ 0) (c : K) :
    Hd h d * U12 h c * Hd h d⁻¹ * U12 h (-c) = U12 h ((d ^ 2 - 1) * c) := by
  rw [Hd_conj_U12 h hd, U12_mul]
  ring_nf

theorem Hd_comm_U21 {d : K} (hd : d ≠ 0) (c : K) :
    Hd h d * U21 h c * Hd h d⁻¹ * U21 h (-c) = U21 h ((d⁻¹ ^ 2 - 1) * c) := by
  rw [Hd_conj_U21 h hd, U21_mul]
  ring_nf

theorem neg_Wm_mul_Wm : -(Wm : Matrix (Fin 4) (Fin 4) K) * Wm = 1 := by
  rw [Matrix.neg_mul, Wm_mul_Wm, neg_neg]

end HBlocks

end CFSG.ComponentClassification.CatFactsL4U4
