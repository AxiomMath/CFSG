module

public import CFSG.Open.StatedDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open Matrix

section Cyc

variable {K : Type} [Field K]

def psuNineCyc (w : K) : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, w, 0; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, w⁻¹]

theorem psuNineCyc_det {w : K} (hw : w ≠ 0) : (psuNineCyc w).det = 1 := by
  rw [psuNineCyc, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero]
  have h : Fin.succAbove (2 : Fin 4) (2 : Fin 3) = 3 := by decide
  simp [h, hw]

theorem psuNineCyc_sq (w : K) :
    psuNineCyc w * psuNineCyc w =
      !![0, w, 0, 0; 0, 0, w, 0; 1, 0, 0, 0; 0, 0, 0, w⁻¹ * w⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [psuNineCyc, Matrix.mul_apply, Fin.sum_univ_four]

theorem psuNineCyc_cube (w : K) :
    psuNineCyc w * psuNineCyc w * psuNineCyc w = diagonal ![w, w, w, w⁻¹ * w⁻¹ * w⁻¹] := by
  rw [psuNineCyc_sq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [psuNineCyc, Matrix.mul_apply, Fin.sum_univ_four]

theorem psuNineCyc_cube_of_pow_three {w : K} (hw : w ^ 3 = 1) :
    psuNineCyc w ^ 3 = diagonal ![w, w, w, 1] := by
  have h1 : w⁻¹ * w⁻¹ * w⁻¹ = 1 := by
    rw [← mul_inv, ← mul_inv, ← pow_three', hw, inv_one]
  rw [pow_three', psuNineCyc_cube, h1]

theorem psuNineCyc_pow_nine {w : K} (hw : w ^ 3 = 1) : psuNineCyc w ^ 9 = 1 := by
  rw [show 9 = 3 * 3 by norm_num, pow_mul, psuNineCyc_cube_of_pow_three hw, diagonal_pow]
  have : (![w, w, w, 1] : Fin 4 → K) ^ 3 = 1 := by
    ext i
    fin_cases i <;> simp [hw]
  rw [this]
  exact diagonal_one

theorem psuNineCyc_unitary {w : K} (hw : w ^ 3 = 1) :
    ((psuNineCyc w).map (· ^ 2))ᵀ * psuNineCyc w = 1 := by
  have hw' : w ^ 2 * w = 1 := by rw [← pow_succ, hw]
  have h2 : (w ^ 2)⁻¹ * w⁻¹ = 1 := by
    rw [← mul_inv, hw', inv_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [psuNineCyc, Matrix.mul_apply, Fin.sum_univ_four, hw', h2]

end Cyc

section Embed

def psuNineEmb (m : ℕ) (K : Type) [Field K] :
    Matrix (Fin 4) (Fin 4) K →* Matrix (Fin (4 + m)) (Fin (4 + m)) K where
  toFun A := Matrix.reindexRingEquiv K finSumFinEquiv (Matrix.fromBlocks A 0 0 1)
  map_one' := by rw [Matrix.fromBlocks_one, map_one]
  map_mul' A B := by
    rw [← map_mul, Matrix.fromBlocks_multiply]
    simp

variable {K : Type} [Field K] {m : ℕ}

theorem psuNineEmb_apply_castAdd (A : Matrix (Fin 4) (Fin 4) K) (i j : Fin 4) :
    psuNineEmb m K A (Fin.castAdd m i) (Fin.castAdd m j) = A i j := by
  simp [psuNineEmb, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem psuNineEmb_transpose (A : Matrix (Fin 4) (Fin 4) K) :
    (psuNineEmb m K A)ᵀ = psuNineEmb m K Aᵀ := by
  simp [psuNineEmb, Matrix.reindex_apply, Matrix.transpose_submatrix,
    Matrix.fromBlocks_transpose]

theorem psuNineEmb_map (f : K → K) (h0 : f 0 = 0) (h1 : f 1 = 1) (A : Matrix (Fin 4) (Fin 4) K) :
    (psuNineEmb m K A).map f = psuNineEmb m K (A.map f) := by
  simp [psuNineEmb, Matrix.reindex_apply, ← Matrix.submatrix_map, Matrix.fromBlocks_map,
    Matrix.map_zero _ h0, Matrix.map_one _ h0 h1]

theorem psuNineEmb_det (A : Matrix (Fin 4) (Fin 4) K) : (psuNineEmb m K A).det = A.det := by
  simp [psuNineEmb, Matrix.det_fromBlocks_zero₂₁]

end Embed

section Main

variable {K : Type} [Field K]

theorem psuNine_exists_orderOf_eq_nine [Finite K] (hK : Nat.card K = 4) (m : ℕ) :
    ∃ x : StatedProj (StatedSU (4 + m) (2 ^ 1) K), orderOf x = 9 := by
  have hU : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rw [hU])
  have hw3 : (u : K) ^ 3 = 1 := by
    have h1 := pow_orderOf_eq_one u
    rw [hu] at h1
    simpa using congrArg Units.val h1
  have hw1 : (u : K) ≠ 1 := by
    intro h1
    have h2 : u = 1 := Units.ext h1
    rw [h2, orderOf_one] at hu
    norm_num at hu
  set N : Matrix (Fin (4 + m)) (Fin (4 + m)) K := psuNineEmb m K (psuNineCyc (u : K)) with hN
  have hN9 : N ^ 9 = 1 := by
    rw [hN, ← map_pow, psuNineCyc_pow_nine hw3, map_one]
  have hN3 : N ^ 3 = psuNineEmb m K (diagonal ![(u : K), u, u, 1]) := by
    rw [hN, ← map_pow, psuNineCyc_cube_of_pow_three hw3]
  let g : GL (Fin (4 + m)) K :=
    ⟨N, N ^ 8, by rw [← pow_succ']; exact hN9, by rw [← pow_succ]; exact hN9⟩
  have hgmem : g ∈ StatedSU (4 + m) (2 ^ 1) K := by
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · show N.det = 1
      rw [hN, psuNineEmb_det, psuNineCyc_det u.ne_zero]
    · show (N.map (· ^ 2))ᵀ * N = 1
      rw [hN, psuNineEmb_map _ (by simp) (by simp), psuNineEmb_transpose, ← map_mul,
        psuNineCyc_unitary hw3, map_one]
  refine ⟨QuotientGroup.mk ⟨g, hgmem⟩, ?_⟩
  have ha9 : (QuotientGroup.mk ⟨g, hgmem⟩ : StatedProj (StatedSU (4 + m) (2 ^ 1) K)) ^ 9 = 1 := by
    rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_one]
    congr 1
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow]
    exact Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hN9)
  have ha3 : ¬ (QuotientGroup.mk ⟨g, hgmem⟩ :
      StatedProj (StatedSU (4 + m) (2 ^ 1) K)) ^ 3 = 1 := by
    intro h1
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow] at h1
    obtain ⟨c, hc⟩ := h1
    have hcm := congrArg
      (Units.val : GL (Fin (4 + m)) K → Matrix (Fin (4 + m)) (Fin (4 + m)) K) hc
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Units.val_pow_eq_pow_val] at hcm
    have e0 := congrFun (congrFun hcm (Fin.castAdd m 0)) (Fin.castAdd m 0)
    have e3 := congrFun (congrFun hcm (Fin.castAdd m 3)) (Fin.castAdd m 3)
    have hN3' : ((g : Matrix (Fin (4 + m)) (Fin (4 + m)) K)) ^ 3 =
        psuNineEmb m K (diagonal ![(u : K), u, u, 1]) := hN3
    rw [hN3', psuNineEmb_apply_castAdd] at e0 e3
    simp at e0 e3
    have e3' : (c : K) = 1 := by simpa using e3
    exact hw1 (e0.symm.trans e3')
  rw [orderOf_eq_prime_pow (p := 3) (n := 1) ha3 ha9]
  norm_num

end Main

theorem exists_orderOf_eq_nine_psu_two {X : Type} [Group X] {n : ℕ}
    (h : CFSG.Open.StatedClassicalModel X .PSU n 2 1) (hn : 4 ≤ n) :
    ∃ x : X, orderOf x = 9 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain ⟨_, K, _, _, hcard, ⟨e⟩⟩ := h
  have hK : Nat.card K = 4 := by rw [hcard]; norm_num
  obtain ⟨x, hx⟩ := psuNine_exists_orderOf_eq_nine hK m
  exact ⟨e.symm x, by rw [MulEquiv.orderOf_eq, hx]⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
