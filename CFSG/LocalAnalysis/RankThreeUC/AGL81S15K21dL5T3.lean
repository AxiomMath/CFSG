module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dL5Mat

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K21dL5Proof

open K21dA8Proof

theorem bf_good3 : bf good3 = ![0, 1, 1, 2, 2] := by decide

@[expose] def blk3 (A C : B2) : Mat5 :=
  !![1, 0, 0, 0, 0;
     0, A 0 0, A 0 1, 0, 0;
     0, A 1 0, A 1 1, 0, 0;
     0, 0, 0, C 0 0, C 0 1;
     0, 0, 0, C 1 0, C 1 1]

@[expose] def blkA3 (M : Mat5) : B2 := !![M 1 1, M 1 2; M 2 1, M 2 2]

@[expose] def blkC3 (M : Mat5) : B2 := !![M 3 3, M 3 4; M 4 3, M 4 4]

theorem blkA3_blk3 (A C : B2) : blkA3 (blk3 A C) = A := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [blkA3, blk3]

theorem blkC3_blk3 (A C : B2) : blkC3 (blk3 A C) = C := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [blkC3, blk3]

theorem blk3_mul (A C A' C' : B2) : blk3 A C * blk3 A' C' = blk3 (A * A') (C * C') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk3, Matrix.mul_apply, Fin.sum_univ_five, Fin.sum_univ_two] <;> ring

theorem blk3_one : blk3 1 1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [blk3]

theorem blk3_inj {A C A' C' : B2} (h : blk3 A C = blk3 A' C') : A = A' ∧ C = C' :=
  ⟨by rw [← blkA3_blk3 A C, h, blkA3_blk3], by rw [← blkC3_blk3 A C, h, blkC3_blk3]⟩

theorem blk3_det (A C : B2) : (blk3 A C).det = A.det * C.det := by
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, blk3, Matrix.det_fin_two,
    Matrix.det_fin_three, Matrix.det_unique]
  simp [Fin.succAbove, Matrix.submatrix]
  ring

theorem blk3_bt (A C : B2) : (blk3 A C).BlockTriangular (bf good3) := by
  intro i j h
  rw [bf_good3] at h
  fin_cases i <;> fin_cases j <;> simp_all [blk3]

theorem blk3_surj (n : SL5)
    (hz : ∀ i j : Fin (4 + 1), bf good3 i ≠ bf good3 j → (n : Mat5) i j = 0) :
    ∃ A C : B2, A.det = 1 ∧ C.det = 1 ∧ (n : Mat5) = blk3 A C := by
  rw [bf_good3] at hz
  have hdet := Matrix.SpecialLinearGroup.det_coe n
  have z01 := hz 0 1 (by decide)
  have z02 := hz 0 2 (by decide)
  have z03 := hz 0 3 (by decide)
  have z04 := hz 0 4 (by decide)
  have z10 := hz 1 0 (by decide)
  have z13 := hz 1 3 (by decide)
  have z14 := hz 1 4 (by decide)
  have z20 := hz 2 0 (by decide)
  have z23 := hz 2 3 (by decide)
  have z24 := hz 2 4 (by decide)
  have z30 := hz 3 0 (by decide)
  have z31 := hz 3 1 (by decide)
  have z32 := hz 3 2 (by decide)
  have z40 := hz 4 0 (by decide)
  have z41 := hz 4 1 (by decide)
  have z42 := hz 4 2 (by decide)
  have hu : (n : Mat5) 0 0 = 1 := by
    by_contra hne
    have key : ∀ x : ZMod 2, x ≠ 1 → x = 0 := by decide
    have h0 := key _ hne
    have : (n : Mat5).det = 0 := by
      refine Matrix.det_eq_zero_of_row_eq_zero 0 fun j => ?_
      fin_cases j
      · exact h0
      · exact z01
      · exact z02
      · exact z03
      · exact z04
    rw [hdet] at this
    exact one_ne_zero this
  have hM : (n : Mat5) = blk3 (blkA3 n) (blkC3 n) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blk3, blkA3, blkC3, hu, z01, z02, z03, z04, z10, z13, z14, z20, z23, z24, z30, z31,
        z32, z40, z41, z42]
  have h1 : (blkA3 n).det * (blkC3 n).det = 1 := by
    rw [← blk3_det, ← hM]
    exact hdet
  exact ⟨blkA3 n, blkC3 n, (zmod2_mul_eq_one _ _ h1).1, (zmod2_mul_eq_one _ _ h1).2, hM⟩

@[expose] def L3 : LevData where
  c := good3
  blk := blk3
  blk_mul := blk3_mul
  blk_one := blk3_one
  blk_inj := fun _ _ _ _ h => blk3_inj h
  blk_det := blk3_det
  blk_bt := blk3_bt
  blk_surj := blk3_surj

theorem s2_upper3 : s2 L3 ∈ upperSub5 := by
  rw [ub5_mem_iff]
  intro i j h
  show (blk3 1 (Ta 1)) i j = 0
  fin_cases i <;> fin_cases j <;> simp_all [blk3, Ta]

theorem triv3 {g : SL5} (hg : g ∈ upperSub5) (hn : g ∈ Subgroup.normalizer (E0 L3 : Set SL5))
    (hc : g ∈ Subgroup.centralizer ({eAB L3} : Set SL5)) : g = 1 := by
  have hb := ub5_mem_iff.1 hg
  have hd := ub5_diag hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hc
  have hc' : (g : Mat5) * blk3 (R3 1) (R3 1) = blk3 (R3 1) (R3 1) * (g : Mat5) := by
    have := congrArg (fun x : SL5 => (x : Mat5)) hc
    simp only [Matrix.SpecialLinearGroup.coe_mul] at this
    exact this
  obtain ⟨i, j, hij⟩ := (Subgroup.mem_normalizer_iff.1 hn (eA L3)).1 (eA_mem L3)
  have hn' : (g : Mat5) * blk3 (R3 1) (R3 0) = blk3 (R3 i) (R3 j) * (g : Mat5) := by
    have h3 : g * eA L3 = (g * eA L3 * g⁻¹) * g := by group
    change (g : Mat5) * (eA L3 : Mat5) = (L3.blk (R3 i) (R3 j)) * (g : Mat5)
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
  have y11 : (g : Mat5) 1 2 = 0 := by
    have e := congrFun (congrFun hc' 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_five, blk3, R3, d0, d1, d2, d3, d4, z10, z20, z30, z40, z21,
      z31, z41, z32, z42, z43] using e
  have y33 : (g : Mat5) 3 4 = 0 := by
    have e := congrFun (congrFun hc' 3) 3
    simpa [Matrix.mul_apply, Fin.sum_univ_five, blk3, R3, d0, d1, d2, d3, d4, z10, z20, z30, z40, z21,
      z31, z41, z32, z42, z43] using e
  have y01 : (g : Mat5) 0 2 = (g : Mat5) 0 1 := by
    have e := congrFun (congrFun hc' 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_five, blk3, R3, d0, d1, d2, d3, d4, z10, z20, z30, z40, z21,
      z31, z41, z32, z42, z43] using e
  have y02 : (g : Mat5) 0 1 + (g : Mat5) 0 2 = (g : Mat5) 0 2 := by
    have e := congrFun (congrFun hc' 0) 2
    simpa [Matrix.mul_apply, Fin.sum_univ_five, blk3, R3, d0, d1, d2, d3, d4, z10, z20, z30, z40, z21,
      z31, z41, z32, z42, z43] using e
  have y03 : (g : Mat5) 0 4 = (g : Mat5) 0 3 := by
    have e := congrFun (congrFun hc' 0) 3
    simpa [Matrix.mul_apply, Fin.sum_univ_five, blk3, R3, d0, d1, d2, d3, d4, z10, z20, z30, z40, z21,
      z31, z41, z32, z42, z43] using e
  have y04 : (g : Mat5) 0 3 + (g : Mat5) 0 4 = (g : Mat5) 0 4 := by
    have e := congrFun (congrFun hc' 0) 4
    simpa [Matrix.mul_apply, Fin.sum_univ_five, blk3, R3, d0, d1, d2, d3, d4, z10, z20, z30, z40, z21,
      z31, z41, z32, z42, z43] using e
  have n11 : (g : Mat5) 1 2 = (R3 i) 0 0 := by
    have e := congrFun (congrFun hn' 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_five, blk3, R3, d0, d1, d2, d3, d4, z10, z20, z30, z40, z21,
      z31, z41, z32, z42, z43] using e
  have n13 : (g : Mat5) 1 3 = (R3 i) 0 0 * (g : Mat5) 1 3 + (R3 i) 0 1 * (g : Mat5) 2 3 := by
    have e := congrFun (congrFun hn' 1) 3
    simpa [Matrix.mul_apply, Fin.sum_univ_five, blk3, R3, d0, d1, d2, d3, d4, z10, z20, z30, z40, z21,
      z31, z41, z32, z42, z43] using e
  have n14 : (g : Mat5) 1 4 = (R3 i) 0 0 * (g : Mat5) 1 4 + (R3 i) 0 1 * (g : Mat5) 2 4 := by
    have e := congrFun (congrFun hn' 1) 4
    simpa [Matrix.mul_apply, Fin.sum_univ_five, blk3, R3, d0, d1, d2, d3, d4, z10, z20, z30, z40, z21,
      z31, z41, z32, z42, z43] using e
  have n23 : (g : Mat5) 2 3 = (R3 i) 1 0 * (g : Mat5) 1 3 + (R3 i) 1 1 * (g : Mat5) 2 3 := by
    have e := congrFun (congrFun hn' 2) 3
    simpa [Matrix.mul_apply, Fin.sum_univ_five, blk3, R3, d0, d1, d2, d3, d4, z10, z20, z30, z40, z21,
      z31, z41, z32, z42, z43] using e
  have n24 : (g : Mat5) 2 4 = (R3 i) 1 0 * (g : Mat5) 1 4 + (R3 i) 1 1 * (g : Mat5) 2 4 := by
    have e := congrFun (congrFun hn' 2) 4
    simpa [Matrix.mul_apply, Fin.sum_univ_five, blk3, R3, d0, d1, d2, d3, d4, z10, z20, z30, z40, z21,
      z31, z41, z32, z42, z43] using e
  have key1 : ∀ i : Fin 3, (R3 i) 0 0 = 0 → i = 1 := by decide
  have hi : i = 1 := key1 i (by rw [← n11]; exact y11)
  subst hi
  have n13' : (g : Mat5) 1 3 = (g : Mat5) 2 3 := by simpa [R3] using n13
  have n23' : (g : Mat5) 2 3 = (g : Mat5) 1 3 + (g : Mat5) 2 3 := by simpa [R3] using n23
  have n14' : (g : Mat5) 1 4 = (g : Mat5) 2 4 := by simpa [R3] using n14
  have n24' : (g : Mat5) 2 4 = (g : Mat5) 1 4 + (g : Mat5) 2 4 := by simpa [R3] using n24
  have k1 : ∀ x y : ZMod 2, x = y → y = x + y → x = 0 ∧ y = 0 := by decide
  have k2 : ∀ x y : ZMod 2, y = x → x + y = y → x = 0 ∧ y = 0 := by decide
  obtain ⟨h01, h02⟩ := k2 _ _ y01 y02
  obtain ⟨h03, h04⟩ := k2 _ _ y03 y04
  obtain ⟨h13, h23⟩ := k1 _ _ n13' n23'
  obtain ⟨h14, h24⟩ := k1 _ _ n14' n24'
  have h12 := y11
  have h34 := y33
  apply Matrix.SpecialLinearGroup.ext
  intro a b
  fin_cases a <;> fin_cases b <;>
    simp [d0, d1, d2, d3, d4, z10, z20, z30, z40, z21, z31, z41, z32, z42, z43, h01, h02, h03, h04,
      h12, h13, h14, h23, h24, h34]

theorem concl_good3 {E : Subgroup SL5} (hE : E ≤ Block good3) (hEc : Nat.card E = 9) :
    K21dConcl upperSub5 E :=
  concl_of_levData L3 s2_upper3 (fun _ hg hn hc => triv3 hg hn hc) hE hEc

end K21dL5Proof

end CFSG.LocalAnalysis.RankThreeUC.S15
