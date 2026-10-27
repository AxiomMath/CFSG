module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dL5Mat

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K21dL5Proof

open K21dA8Proof

theorem bf_good1 : bf good1 = ![0, 0, 1, 1, 2] := by decide

@[expose] def blk1 (A C : B2) : Mat5 :=
  !![A 0 0, A 0 1, 0, 0, 0;
     A 1 0, A 1 1, 0, 0, 0;
     0, 0, C 0 0, C 0 1, 0;
     0, 0, C 1 0, C 1 1, 0;
     0, 0, 0, 0, 1]

@[expose] def blkA1 (M : Mat5) : B2 := !![M 0 0, M 0 1; M 1 0, M 1 1]

@[expose] def blkC1 (M : Mat5) : B2 := !![M 2 2, M 2 3; M 3 2, M 3 3]

theorem blkA1_blk1 (A C : B2) : blkA1 (blk1 A C) = A := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [blkA1, blk1]

theorem blkC1_blk1 (A C : B2) : blkC1 (blk1 A C) = C := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [blkC1, blk1]

theorem blk1_mul (A C A' C' : B2) : blk1 A C * blk1 A' C' = blk1 (A * A') (C * C') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk1, Matrix.mul_apply, Fin.sum_univ_five, Fin.sum_univ_two] <;> ring

theorem blk1_one : blk1 1 1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [blk1]

theorem blk1_inj {A C A' C' : B2} (h : blk1 A C = blk1 A' C') : A = A' ∧ C = C' :=
  ⟨by rw [← blkA1_blk1 A C, h, blkA1_blk1], by rw [← blkC1_blk1 A C, h, blkC1_blk1]⟩

theorem blk1_det (A C : B2) : (blk1 A C).det = A.det * C.det := by
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, blk1, Matrix.det_fin_two,
    Matrix.det_fin_three, Matrix.det_unique]
  simp [Fin.succAbove, Matrix.submatrix]
  ring

theorem blk1_bt (A C : B2) : (blk1 A C).BlockTriangular (bf good1) := by
  intro i j h
  rw [bf_good1] at h
  fin_cases i <;> fin_cases j <;> simp_all [blk1]

theorem blk1_surj (n : SL5)
    (hz : ∀ i j : Fin (4 + 1), bf good1 i ≠ bf good1 j → (n : Mat5) i j = 0) :
    ∃ A C : B2, A.det = 1 ∧ C.det = 1 ∧ (n : Mat5) = blk1 A C := by
  rw [bf_good1] at hz
  have hdet := Matrix.SpecialLinearGroup.det_coe n
  have z02 := hz 0 2 (by decide)
  have z03 := hz 0 3 (by decide)
  have z04 := hz 0 4 (by decide)
  have z12 := hz 1 2 (by decide)
  have z13 := hz 1 3 (by decide)
  have z14 := hz 1 4 (by decide)
  have z20 := hz 2 0 (by decide)
  have z21 := hz 2 1 (by decide)
  have z24 := hz 2 4 (by decide)
  have z30 := hz 3 0 (by decide)
  have z31 := hz 3 1 (by decide)
  have z34 := hz 3 4 (by decide)
  have z40 := hz 4 0 (by decide)
  have z41 := hz 4 1 (by decide)
  have z42 := hz 4 2 (by decide)
  have z43 := hz 4 3 (by decide)
  have hu : (n : Mat5) 4 4 = 1 := by
    by_contra hne
    have key : ∀ x : ZMod 2, x ≠ 1 → x = 0 := by decide
    have h0 := key _ hne
    have : (n : Mat5).det = 0 := by
      refine Matrix.det_eq_zero_of_row_eq_zero 4 fun j => ?_
      fin_cases j
      · exact z40
      · exact z41
      · exact z42
      · exact z43
      · exact h0
    rw [hdet] at this
    exact one_ne_zero this
  have hM : (n : Mat5) = blk1 (blkA1 n) (blkC1 n) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blk1, blkA1, blkC1, hu, z02, z03, z04, z12, z13, z14, z20, z21, z24, z30, z31, z34,
        z40, z41, z42, z43]
  have h1 : (blkA1 n).det * (blkC1 n).det = 1 := by
    rw [← blk1_det, ← hM]
    exact hdet
  exact ⟨blkA1 n, blkC1 n, (zmod2_mul_eq_one _ _ h1).1, (zmod2_mul_eq_one _ _ h1).2, hM⟩

@[expose] def L1 : LevData where
  c := good1
  blk := blk1
  blk_mul := blk1_mul
  blk_one := blk1_one
  blk_inj := fun _ _ _ _ h => blk1_inj h
  blk_det := blk1_det
  blk_bt := blk1_bt
  blk_surj := blk1_surj

theorem s2_upper1 : s2 L1 ∈ upperSub5 := by
  rw [ub5_mem_iff]
  intro i j h
  show (blk1 1 (Ta 1)) i j = 0
  fin_cases i <;> fin_cases j <;> simp_all [blk1, Ta]

theorem triv1 {g : SL5} (hg : g ∈ upperSub5) (hn : g ∈ Subgroup.normalizer (E0 L1 : Set SL5))
    (hc : g ∈ Subgroup.centralizer ({eAB L1} : Set SL5)) : g = 1 := by
  have hb := ub5_mem_iff.1 hg
  have hd := ub5_diag hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hc
  have hc' : (g : Mat5) * blk1 (R3 1) (R3 1) = blk1 (R3 1) (R3 1) * (g : Mat5) := by
    have := congrArg (fun x : SL5 => (x : Mat5)) hc
    simp only [Matrix.SpecialLinearGroup.coe_mul] at this
    exact this
  obtain ⟨i, j, hij⟩ := (Subgroup.mem_normalizer_iff.1 hn (eA L1)).1 (eA_mem L1)
  have hn' : (g : Mat5) * blk1 (R3 1) (R3 0) = blk1 (R3 i) (R3 j) * (g : Mat5) := by
    have h3 : g * eA L1 = (g * eA L1 * g⁻¹) * g := by group
    change (g : Mat5) * (eA L1 : Mat5) = (L1.blk (R3 i) (R3 j)) * (g : Mat5)
    rw [← hij, ← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, ← h3]
  have d0 := hd 0
  have d1 := hd 1
  have d2 := hd 2
  have d3 := hd 3
  have d4 := hd 4
  have z10 := hb 1 0 (by decide)
  have z20 := hb 2 0 (by decide)
  have z30 := hb 3 0 (by decide)
  have z40 := hb 4 0 (by decide)
  have z21 := hb 2 1 (by decide)
  have z31 := hb 3 1 (by decide)
  have z41 := hb 4 1 (by decide)
  have z32 := hb 3 2 (by decide)
  have z42 := hb 4 2 (by decide)
  have z43 := hb 4 3 (by decide)
  have y00 : (g : Mat5) 0 1 = 0 := by
    have e := congrFun (congrFun hc' 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_five, blk1, R3, d0, d1, d2, d3, d4, z10, z20, z30, z40, z21,
      z31, z41, z32, z42, z43] using e
  have y22 : (g : Mat5) 2 3 = 0 := by
    have e := congrFun (congrFun hc' 2) 2
    simpa [Matrix.mul_apply, Fin.sum_univ_five, blk1, R3, d0, d1, d2, d3, d4, z10, z20, z30, z40, z21,
      z31, z41, z32, z42, z43] using e
  have y04 : (g : Mat5) 0 4 = (g : Mat5) 1 4 := by
    have e := congrFun (congrFun hc' 0) 4
    simpa [Matrix.mul_apply, Fin.sum_univ_five, blk1, R3, d0, d1, d2, d3, d4, z10, z20, z30, z40, z21,
      z31, z41, z32, z42, z43] using e
  have y14 : (g : Mat5) 1 4 = (g : Mat5) 0 4 + (g : Mat5) 1 4 := by
    have e := congrFun (congrFun hc' 1) 4
    simpa [Matrix.mul_apply, Fin.sum_univ_five, blk1, R3, d0, d1, d2, d3, d4, z10, z20, z30, z40, z21,
      z31, z41, z32, z42, z43] using e
  have y24 : (g : Mat5) 2 4 = (g : Mat5) 3 4 := by
    have e := congrFun (congrFun hc' 2) 4
    simpa [Matrix.mul_apply, Fin.sum_univ_five, blk1, R3, d0, d1, d2, d3, d4, z10, z20, z30, z40, z21,
      z31, z41, z32, z42, z43] using e
  have y34 : (g : Mat5) 3 4 = (g : Mat5) 2 4 + (g : Mat5) 3 4 := by
    have e := congrFun (congrFun hc' 3) 4
    simpa [Matrix.mul_apply, Fin.sum_univ_five, blk1, R3, d0, d1, d2, d3, d4, z10, z20, z30, z40, z21,
      z31, z41, z32, z42, z43] using e
  have n00 : (g : Mat5) 0 1 = (R3 i) 0 0 := by
    have e := congrFun (congrFun hn' 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_five, blk1, R3, d0, d1, d2, d3, d4, z10, z20, z30, z40, z21,
      z31, z41, z32, z42, z43] using e
  have n02 : (g : Mat5) 0 2 = (R3 i) 0 0 * (g : Mat5) 0 2 + (R3 i) 0 1 * (g : Mat5) 1 2 := by
    have e := congrFun (congrFun hn' 0) 2
    simpa [Matrix.mul_apply, Fin.sum_univ_five, blk1, R3, d0, d1, d2, d3, d4, z10, z20, z30, z40, z21,
      z31, z41, z32, z42, z43] using e
  have n03 : (g : Mat5) 0 3 = (R3 i) 0 0 * (g : Mat5) 0 3 + (R3 i) 0 1 * (g : Mat5) 1 3 := by
    have e := congrFun (congrFun hn' 0) 3
    simpa [Matrix.mul_apply, Fin.sum_univ_five, blk1, R3, d0, d1, d2, d3, d4, z10, z20, z30, z40, z21,
      z31, z41, z32, z42, z43] using e
  have n12 : (g : Mat5) 1 2 = (R3 i) 1 0 * (g : Mat5) 0 2 + (R3 i) 1 1 * (g : Mat5) 1 2 := by
    have e := congrFun (congrFun hn' 1) 2
    simpa [Matrix.mul_apply, Fin.sum_univ_five, blk1, R3, d0, d1, d2, d3, d4, z10, z20, z30, z40, z21,
      z31, z41, z32, z42, z43] using e
  have n13 : (g : Mat5) 1 3 = (R3 i) 1 0 * (g : Mat5) 0 3 + (R3 i) 1 1 * (g : Mat5) 1 3 := by
    have e := congrFun (congrFun hn' 1) 3
    simpa [Matrix.mul_apply, Fin.sum_univ_five, blk1, R3, d0, d1, d2, d3, d4, z10, z20, z30, z40, z21,
      z31, z41, z32, z42, z43] using e
  have key1 : ∀ i : Fin 3, (R3 i) 0 0 = 0 → i = 1 := by decide
  have hi : i = 1 := key1 i (by rw [← n00]; exact y00)
  subst hi
  have n02' : (g : Mat5) 0 2 = (g : Mat5) 1 2 := by simpa [R3] using n02
  have n12' : (g : Mat5) 1 2 = (g : Mat5) 0 2 + (g : Mat5) 1 2 := by simpa [R3] using n12
  have n03' : (g : Mat5) 0 3 = (g : Mat5) 1 3 := by simpa [R3] using n03
  have n13' : (g : Mat5) 1 3 = (g : Mat5) 0 3 + (g : Mat5) 1 3 := by simpa [R3] using n13
  have k1 : ∀ x y : ZMod 2, x = y → y = x + y → x = 0 ∧ y = 0 := by decide
  obtain ⟨h04, h14⟩ := k1 _ _ y04 y14
  obtain ⟨h24, h34⟩ := k1 _ _ y24 y34
  obtain ⟨h02, h12⟩ := k1 _ _ n02' n12'
  obtain ⟨h03, h13⟩ := k1 _ _ n03' n13'
  have h01 := y00
  have h23 := y22
  apply Matrix.SpecialLinearGroup.ext
  intro a b
  fin_cases a <;> fin_cases b <;>
    simp [d0, d1, d2, d3, d4, z10, z20, z30, z40, z21, z31, z41, z32, z42, z43, h01, h02, h03, h04,
      h12, h13, h14, h23, h24, h34]

theorem concl_good1 {E : Subgroup SL5} (hE : E ≤ Block good1) (hEc : Nat.card E = 9) :
    K21dConcl upperSub5 E :=
  concl_of_levData L1 s2_upper1 (fun _ hg hn hc => triv1 hg hn hc) hE hEc

end K21dL5Proof

end CFSG.LocalAnalysis.RankThreeUC.S15
