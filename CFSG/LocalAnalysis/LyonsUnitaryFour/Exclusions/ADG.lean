module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Exclusions.Tools
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Enumeration.ExclusionArithmetic
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

open scoped BigOperators

namespace CFSG.LyonsUnitaryFour

variable {ι : Type*} [DecidableEq ι] {B : Finset ι} {row : ι → LyonsRow} {f : ι → ℤ} {p : ι}
  {N : ℕ} {P : ℚ}

theorem lyons_signedDegree_ne_A1 (hD : LyonsSignedDegreeData B row f p N P) :
    B.val.map row ≠ lyonsConfiguration .A1 := by
  intro hM
  have hcount : ∀ R, (B.val.map row).count R = (lyonsConfiguration .A1).count R :=
    fun R => by rw [hM]
  obtain ⟨χq, hq, hrq, huq⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (-2, 2, 2, 2, 2, 2)) (by rw [hcount]; decide)
  obtain ⟨χ1, h1, hr1, hu1⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (-1, 1, -1, 1, 1, 1)) (by rw [hcount]; decide)
  obtain ⟨χ2, h2, hr2, hu2⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (-1, 1, 1, -1, 1, 1)) (by rw [hcount]; decide)
  obtain ⟨χ3, h3, hr3, hu3⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (-1, 1, 1, 1, -1, 1)) (by rw [hcount]; decide)
  obtain ⟨χ4, h4, hr4, hu4⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (-1, 1, 1, 1, 1, -1)) (by rw [hcount]; decide)
  obtain ⟨χz, hz, hrz, huz⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (1, 1, 2, 2, 2, 2)) (by rw [hcount]; decide)
  obtain ⟨χw, hw, hrw, huw⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (2, 2, 2, 2, 2, 2)) (by rw [hcount]; decide)
  obtain ⟨y1, y2, hy1p, hy2p, hy12, hfibP⟩ := rowFiber_eq_triple hD.principal_mem
    hD.principal_row (by rw [hcount]; decide)
  have hy1 : y1 ∈ B ∧ row y1 = principalRow := mem_rowFiber.mp (by rw [hfibP]; simp)
  have hy2 : y2 ∈ B ∧ row y2 = principalRow := mem_rowFiber.mp (by rw [hfibP]; simp)
  obtain ⟨τ, hτ, hτrow⟩ := hD.galois
  have hf2 : f χ2 = f χ1 := degree_rotate_eq τ hτ hτrow h1 (by rw [hr2, hr1]; decide)
    (fun φ hφ e => hu2 φ hφ (e.trans hr2))
  have hf3 : f χ3 = f χ2 := degree_rotate_eq τ hτ hτrow h2 (by rw [hr3, hr2]; decide)
    (fun φ hφ e => hu3 φ hφ (e.trans hr3))
  have hf4 : f χ4 = f χ3 := degree_rotate_eq τ hτ hτrow h3 (by rw [hr4, hr3]; decide)
    (fun φ hφ e => hu4 φ hφ (e.trans hr4))
  have fq := rowFiber_eq_singleton hq hrq huq
  have f1 := rowFiber_eq_singleton h1 hr1 hu1
  have f2 := rowFiber_eq_singleton h2 hr2 hu2
  have f3 := rowFiber_eq_singleton h3 hr3 hu3
  have f4 := rowFiber_eq_singleton h4 hr4 hu4
  have fz := rowFiber_eq_singleton hz hrz huz
  have fw := rowFiber_eq_singleton hw hrw huw
  have hpy : p ∉ ({y1, y2} : Finset ι) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hy1p h.symm, fun h => hy2p h.symm⟩
  have hy1y2 : y1 ∉ ({y2} : Finset ι) := by simpa using hy12
  have hsum : ∀ k, ∑ χ ∈ B, (((row χ).toVec k : ℤ) : ℚ) * (f χ : ℚ) = 0 := by
    intro k
    have := hD.degree_eq k
    have hcast := congrArg (fun n : ℤ => (n : ℚ)) this
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_zero] at hcast
    rw [← hcast]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hrec : ∀ k, ∑ χ ∈ B, (((row χ).fourierSum : ℚ) ^ 2 * (row χ).toVec k) *
      ((f χ : ℚ))⁻¹ = if k = 0 then 0 else P := by
    intro k
    by_cases hk : k = 0
    · subst hk
      rw [ite_eq_left rfl, ← hD.reciprocal_u]
      refine Finset.sum_congr rfl fun χ _ => ?_
      rw [div_eq_mul_inv]
      rfl
    · rw [ite_eq_right hk, ← hD.reciprocal_v k hk]
      exact Finset.sum_congr rfl fun χ _ => by rw [div_eq_mul_inv]
  have expand : ∀ (G : LyonsRow → ℚ) (H : ι → ℚ), ∑ χ ∈ B, G (row χ) * H χ =
      G (-2, 2, 2, 2, 2, 2) * H χq + G (-1, 1, -1, 1, 1, 1) * H χ1 +
        G (-1, 1, 1, -1, 1, 1) * H χ2 + G (-1, 1, 1, 1, -1, 1) * H χ3 +
        G (-1, 1, 1, 1, 1, -1) * H χ4 + G (1, 1, 0, 0, 0, 0) * (H p + (H y1 + H y2)) +
        G (1, 1, 2, 2, 2, 2) * H χz + G (2, 2, 2, 2, 2, 2) * H χw := by
    intro G H
    rw [sum_mul_row_eq hM G H]
    simp only [LyonsLabel.rows, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]
    rw [fq, f1, f2, f3, f4, fz, fw, show ((1, 1, 0, 0, 0, 0) : LyonsRow) = principalRow from rfl,
      hfibP, Finset.sum_insert hpy, Finset.sum_insert hy1y2]
    simp only [Finset.sum_singleton]
    ring
  have hfp : (f p : ℚ) = 1 := by rw [hD.principal_degree]; simp
  have e_au := hsum 1
  have e_u := hsum 0
  have e_b := hsum 2
  rw [expand (fun R => ((R.toVec 1 : ℤ) : ℚ)) (fun χ => (f χ : ℚ))] at e_au
  rw [expand (fun R => ((R.toVec 0 : ℤ) : ℚ)) (fun χ => (f χ : ℚ))] at e_u
  rw [expand (fun R => ((R.toVec 2 : ℤ) : ℚ)) (fun χ => (f χ : ℚ))] at e_b
  have r_a := hrec 1
  have r_u := hrec 0
  have r_b := hrec 2
  rw [expand (fun R => ((R.fourierSum : ℚ) ^ 2 * (R.toVec 1 : ℚ)))
    (fun χ => ((f χ : ℚ))⁻¹)] at r_a
  rw [expand (fun R => ((R.fourierSum : ℚ) ^ 2 * (R.toVec 0 : ℚ)))
    (fun χ => ((f χ : ℚ))⁻¹)] at r_u
  rw [expand (fun R => ((R.fourierSum : ℚ) ^ 2 * (R.toVec 2 : ℚ)))
    (fun χ => ((f χ : ℚ))⁻¹)] at r_b
  simp only [LyonsRow.toVec, LyonsRow.fourierSum, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Fin.isValue, Int.cast_neg, Int.cast_one, Int.cast_ofNat,
    hfp, hf2, hf3, hf4] at e_au e_u e_b r_a r_u r_b
  norm_num at e_au e_u e_b r_a r_u r_b
  have hres : ∀ χ ∈ B, ∀ R : LyonsRow, row χ = R →
      (64 : ℤ) ∣ f χ + 3 * R.fourierSum + 60 * R.1 := by
    intro χ hχ R hR
    have := hD.mult_a_dvd χ hχ
    rwa [hR] at this
  have cx : f χ1 ≡ 51 [ZMOD 64] := by
    have := hres χ1 h1 _ hr1
    simp only [LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have cy₁ : f y1 ≡ 1 [ZMOD 64] := by
    have := hres y1 hy1.1 _ hy1.2
    simp only [principalRow, LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have cy₂ : f y2 ≡ 1 [ZMOD 64] := by
    have := hres y2 hy2.1 _ hy2.2
    simp only [principalRow, LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have cz : f χz ≡ 41 [ZMOD 64] := by
    have := hres χz hz _ hrz
    simp only [LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have hq90 : 0 < f χq → 90 ≤ f χq := by
    intro hpos
    have h := hD.mult_a_nonneg χq hq
    rw [hrq] at h
    simp only [LyonsRow.fourierSum] at h
    have hs : Int.sign (f χq) = 1 := Int.sign_eq_one_of_pos hpos
    rw [hs, one_mul] at h
    omega
  have hy₁ : 12 ≤ |f y1| := hD.degree_ge y1 hy1.1 hy1p
  have hy₂ : 12 ≤ |f y2| := hD.degree_ge y2 hy2.1 hy2p
  apply lyons_ADG_arithmetic (f χ1) (f χq) (f y1) (f y2) (f χz) hy₁ hy₂ cx cy₁ cy₂ cz hq90
  · have : (8 * f χ1 + 4 * f χq : ℚ) = 0 := by linear_combination e_au - e_u
    exact_mod_cast this
  · have hP := hD.P_pos
    have : (72 : ℚ) / f χ1 + 400 / f χq = P := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      linear_combination r_a - r_u
    rw [this]; exact hP
  · have : (1 + 2 * f χ1 + f y1 + f y2 - f χz : ℚ) = 0 := by linear_combination e_au - e_b
    exact_mod_cast this
  · simp only [div_eq_mul_inv]
    linear_combination r_a - r_b

omit [DecidableEq ι] in
theorem lyons_signedDegree_ne_A2 (hD : LyonsSignedDegreeData B row f p N P) :
    B.val.map row ≠ lyonsConfiguration .A2 := by
  intro hM
  obtain ⟨χq, hq, hrq, Fq, Iq⟩ :=
    exists_fiber_single (f := f) (R := (-2, 2, 2, 2, 2, 2)) (by rw [hM]; decide)
  obtain ⟨χx, hx, hrx, Fx, Ix⟩ :=
    exists_fiber_single (f := f) (R := (-1, 1, 0, 0, 0, 2)) (by rw [hM]; decide)
  obtain ⟨χz, hz, hrz, Fz, Iz⟩ :=
    exists_fiber_single (f := f) (R := (1, 1, 2, 2, 2, 2)) (by rw [hM]; decide)
  obtain ⟨y₁, hy₁, y₂, hy₂, hry₁, hry₂, hy₁p, hy₂p, Fp, Ip⟩ :=
    hD.exists_fiber_principal_triple (by rw [hM]; decide)
  rw [principalRow] at Fp Ip
  obtain ⟨F₂, F₃, F₄, I₂, I₃, I₄⟩ := hD.fiber_rotate_cycle (-1, 1, 0, 0, 0, 2)
  simp only [LyonsRow.rotate] at F₂ F₃ F₄ I₂ I₃ I₄
  have e_u := hD.degree_eq_rows hM 0
  have e_a := hD.degree_eq_rows hM 1
  have e_b := hD.degree_eq_rows hM 2
  have r_u := hD.reciprocal_rows_zero hM
  have r_a := hD.reciprocal_rows hM 1 (by decide)
  have r_b := hD.reciprocal_rows hM 2 (by decide)
  simp only [LyonsLabel.rows, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    LyonsRow.toVec, LyonsRow.fourierSum, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue, F₂, F₃, F₄,
    I₂, I₃, I₄, Fq, Fx, Fz, Fp, Iq, Ix, Iz, Ip] at e_u e_a e_b r_u r_a r_b
  push_cast at e_u e_a e_b r_u r_a r_b
  apply lyons_ADG_arithmetic (f χx) (f χq) (f y₁) (f y₂) (f χz)
    (hD.degree_ge y₁ hy₁ hy₁p) (hD.degree_ge y₂ hy₂ hy₂p)
    (hD.modEq_of_row hx hrx (by decide)) (hD.modEq_of_row hy₁ hry₁ (by decide))
    (hD.modEq_of_row hy₂ hry₂ (by decide)) (hD.modEq_of_row hz hrz (by decide))
    (hD.le_of_pos_of_row hq hrq (by decide))
  · exact_mod_cast (by linear_combination e_a - e_u : (8 * f χx + 4 * f χq : ℚ) = 0)
  · have h : (72 : ℚ) / f χx + 400 / f χq = P := by
      simp only [div_eq_mul_inv]
      linear_combination r_a - r_u
    rw [h]
    exact hD.P_pos
  · exact_mod_cast
      (by linear_combination e_a - e_b : (1 + 2 * f χx + f y₁ + f y₂ - f χz : ℚ) = 0)
  · simp only [div_eq_mul_inv]
    linear_combination r_a - r_b

omit [DecidableEq ι] in
theorem lyons_signedDegree_ne_D1 (hD : LyonsSignedDegreeData B row f p N P) :
    B.val.map row ≠ lyonsConfiguration .D1 := by
  intro hM
  obtain ⟨χq, hq, hrq, Fq, Iq⟩ :=
    exists_fiber_single (f := f) (R := (-2, 2, 2, 2, 2, 2)) (by rw [hM]; decide)
  obtain ⟨χx, hx, hrx, Fx, Ix⟩ :=
    exists_fiber_single (f := f) (R := (-1, 1, -1, 1, 1, 1)) (by rw [hM]; decide)
  obtain ⟨χz, hz, hrz, Fz, Iz⟩ :=
    exists_fiber_single (f := f) (R := (1, 1, 2, 2, 2, 2)) (by rw [hM]; decide)
  obtain ⟨y₁, hy₁, y₂, hy₂, hry₁, hry₂, hy₁p, hy₂p, Fp, Ip⟩ :=
    hD.exists_fiber_principal_triple (by rw [hM]; decide)
  rw [principalRow] at Fp Ip
  obtain ⟨F₂, F₃, F₄, I₂, I₃, I₄⟩ := hD.fiber_rotate_cycle (-1, 1, -1, 1, 1, 1)
  simp only [LyonsRow.rotate] at F₂ F₃ F₄ I₂ I₃ I₄
  have e_u := hD.degree_eq_rows hM 0
  have e_a := hD.degree_eq_rows hM 1
  have e_b := hD.degree_eq_rows hM 2
  have r_u := hD.reciprocal_rows_zero hM
  have r_a := hD.reciprocal_rows hM 1 (by decide)
  have r_b := hD.reciprocal_rows hM 2 (by decide)
  simp only [LyonsLabel.rows, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    LyonsRow.toVec, LyonsRow.fourierSum, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue, F₂, F₃, F₄,
    I₂, I₃, I₄, Fq, Fx, Fz, Fp, Iq, Ix, Iz, Ip] at e_u e_a e_b r_u r_a r_b
  push_cast at e_u e_a e_b r_u r_a r_b
  apply lyons_ADG_arithmetic (f χx) (f χq) (f y₁) (f y₂) (f χz)
    (hD.degree_ge y₁ hy₁ hy₁p) (hD.degree_ge y₂ hy₂ hy₂p)
    (hD.modEq_of_row hx hrx (by decide)) (hD.modEq_of_row hy₁ hry₁ (by decide))
    (hD.modEq_of_row hy₂ hry₂ (by decide)) (hD.modEq_of_row hz hrz (by decide))
    (hD.le_of_pos_of_row hq hrq (by decide))
  · exact_mod_cast (by linear_combination e_a - e_u : (8 * f χx + 4 * f χq : ℚ) = 0)
  · have h : (72 : ℚ) / f χx + 400 / f χq = P := by
      simp only [div_eq_mul_inv]
      linear_combination r_a - r_u
    rw [h]
    exact hD.P_pos
  · exact_mod_cast
      (by linear_combination e_a - e_b : (1 + 2 * f χx + f y₁ + f y₂ - f χz : ℚ) = 0)
  · simp only [div_eq_mul_inv]
    linear_combination r_a - r_b

omit [DecidableEq ι] in
theorem lyons_signedDegree_ne_D2 (hD : LyonsSignedDegreeData B row f p N P) :
    B.val.map row ≠ lyonsConfiguration .D2 := by
  intro hM
  obtain ⟨χq, hq, hrq, Fq, Iq⟩ :=
    exists_fiber_single (f := f) (R := (-2, 2, 2, 2, 2, 2)) (by rw [hM]; decide)
  obtain ⟨χx, hx, hrx, Fx, Ix⟩ :=
    exists_fiber_single (f := f) (R := (-1, 1, 0, 0, 0, 2)) (by rw [hM]; decide)
  obtain ⟨χz, hz, hrz, Fz, Iz⟩ :=
    exists_fiber_single (f := f) (R := (1, 1, 2, 2, 2, 2)) (by rw [hM]; decide)
  obtain ⟨y₁, hy₁, y₂, hy₂, hry₁, hry₂, hy₁p, hy₂p, Fp, Ip⟩ :=
    hD.exists_fiber_principal_triple (by rw [hM]; decide)
  rw [principalRow] at Fp Ip
  obtain ⟨F₂, F₃, F₄, I₂, I₃, I₄⟩ := hD.fiber_rotate_cycle (-1, 1, 0, 0, 0, 2)
  simp only [LyonsRow.rotate] at F₂ F₃ F₄ I₂ I₃ I₄
  have e_u := hD.degree_eq_rows hM 0
  have e_a := hD.degree_eq_rows hM 1
  have e_b := hD.degree_eq_rows hM 2
  have r_u := hD.reciprocal_rows_zero hM
  have r_a := hD.reciprocal_rows hM 1 (by decide)
  have r_b := hD.reciprocal_rows hM 2 (by decide)
  simp only [LyonsLabel.rows, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    LyonsRow.toVec, LyonsRow.fourierSum, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue, F₂, F₃, F₄,
    I₂, I₃, I₄, Fq, Fx, Fz, Fp, Iq, Ix, Iz, Ip] at e_u e_a e_b r_u r_a r_b
  push_cast at e_u e_a e_b r_u r_a r_b
  apply lyons_ADG_arithmetic (f χx) (f χq) (f y₁) (f y₂) (f χz)
    (hD.degree_ge y₁ hy₁ hy₁p) (hD.degree_ge y₂ hy₂ hy₂p)
    (hD.modEq_of_row hx hrx (by decide)) (hD.modEq_of_row hy₁ hry₁ (by decide))
    (hD.modEq_of_row hy₂ hry₂ (by decide)) (hD.modEq_of_row hz hrz (by decide))
    (hD.le_of_pos_of_row hq hrq (by decide))
  · exact_mod_cast (by linear_combination e_a - e_u : (8 * f χx + 4 * f χq : ℚ) = 0)
  · have h : (72 : ℚ) / f χx + 400 / f χq = P := by
      simp only [div_eq_mul_inv]
      linear_combination r_a - r_u
    rw [h]
    exact hD.P_pos
  · exact_mod_cast
      (by linear_combination e_a - e_b : (1 + 2 * f χx + f y₁ + f y₂ - f χz : ℚ) = 0)
  · simp only [div_eq_mul_inv]
    linear_combination r_a - r_b

omit [DecidableEq ι] in
theorem lyons_signedDegree_ne_G (hD : LyonsSignedDegreeData B row f p N P) :
    B.val.map row ≠ lyonsConfiguration .G := by
  intro hM
  obtain ⟨χq, hq, hrq, Fq, Iq⟩ :=
    exists_fiber_single (f := f) (R := (-2, 2, 2, 2, 2, 2)) (by rw [hM]; decide)
  obtain ⟨χx, hx, hrx, Fx, Ix⟩ :=
    exists_fiber_single (f := f) (R := (-1, 1, 0, 0, 1, 1)) (by rw [hM]; decide)
  obtain ⟨χz, hz, hrz, Fz, Iz⟩ :=
    exists_fiber_single (f := f) (R := (1, 1, 2, 2, 2, 2)) (by rw [hM]; decide)
  obtain ⟨y₁, hy₁, y₂, hy₂, hry₁, hry₂, hy₁p, hy₂p, Fp, Ip⟩ :=
    hD.exists_fiber_principal_triple (by rw [hM]; decide)
  rw [principalRow] at Fp Ip
  obtain ⟨F₂, F₃, F₄, I₂, I₃, I₄⟩ := hD.fiber_rotate_cycle (-1, 1, 0, 0, 1, 1)
  simp only [LyonsRow.rotate] at F₂ F₃ F₄ I₂ I₃ I₄
  obtain ⟨G₂, G₃, G₄, J₂, J₃, J₄⟩ := hD.fiber_rotate_cycle (1, 1, 0, 1, 1, 2)
  simp only [LyonsRow.rotate] at G₂ G₃ G₄ J₂ J₃ J₄
  have e_u := hD.degree_eq_rows hM 0
  have e_a := hD.degree_eq_rows hM 1
  have e_b := hD.degree_eq_rows hM 2
  have r_u := hD.reciprocal_rows_zero hM
  have r_a := hD.reciprocal_rows hM 1 (by decide)
  have r_b := hD.reciprocal_rows hM 2 (by decide)
  simp only [LyonsLabel.rows, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    LyonsRow.toVec, LyonsRow.fourierSum, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue, G₂, G₃, G₄, J₂, J₃,
    J₄, F₂, F₃, F₄, I₂, I₃, I₄, Fq, Fx, Fz, Fp, Iq, Ix, Iz, Ip] at e_u e_a e_b r_u r_a r_b
  push_cast at e_u e_a e_b r_u r_a r_b
  apply lyons_ADG_arithmetic (f χx) (f χq) (f y₁) (f y₂) (f χz)
    (hD.degree_ge y₁ hy₁ hy₁p) (hD.degree_ge y₂ hy₂ hy₂p)
    (hD.modEq_of_row hx hrx (by decide)) (hD.modEq_of_row hy₁ hry₁ (by decide))
    (hD.modEq_of_row hy₂ hry₂ (by decide)) (hD.modEq_of_row hz hrz (by decide))
    (hD.le_of_pos_of_row hq hrq (by decide))
  · exact_mod_cast (by linear_combination e_a - e_u : (8 * f χx + 4 * f χq : ℚ) = 0)
  · have h : (72 : ℚ) / f χx + 400 / f χq = P := by
      simp only [div_eq_mul_inv]
      linear_combination r_a - r_u
    rw [h]
    exact hD.P_pos
  · exact_mod_cast
      (by linear_combination e_a - e_b : (1 + 2 * f χx + f y₁ + f y₂ - f χz : ℚ) = 0)
  · simp only [div_eq_mul_inv]
    linear_combination r_a - r_b

omit [DecidableEq ι] in
theorem lyons_signedDegree_ne_GReflected (hD : LyonsSignedDegreeData B row f p N P) :
    B.val.map row ≠ lyonsConfiguration .GReflected := by
  intro hM
  obtain ⟨χq, hq, hrq, Fq, Iq⟩ :=
    exists_fiber_single (f := f) (R := (-2, 2, 2, 2, 2, 2)) (by rw [hM]; decide)
  obtain ⟨χx, hx, hrx, Fx, Ix⟩ :=
    exists_fiber_single (f := f) (R := (-1, 1, 0, 0, 1, 1)) (by rw [hM]; decide)
  obtain ⟨χz, hz, hrz, Fz, Iz⟩ :=
    exists_fiber_single (f := f) (R := (1, 1, 2, 2, 2, 2)) (by rw [hM]; decide)
  obtain ⟨y₁, hy₁, y₂, hy₂, hry₁, hry₂, hy₁p, hy₂p, Fp, Ip⟩ :=
    hD.exists_fiber_principal_triple (by rw [hM]; decide)
  rw [principalRow] at Fp Ip
  obtain ⟨F₂, F₃, F₄, I₂, I₃, I₄⟩ := hD.fiber_rotate_cycle (-1, 1, 0, 0, 1, 1)
  simp only [LyonsRow.rotate] at F₂ F₃ F₄ I₂ I₃ I₄
  obtain ⟨G₂, G₃, G₄, J₂, J₃, J₄⟩ := hD.fiber_rotate_cycle (1, 1, 0, 2, 1, 1)
  simp only [LyonsRow.rotate] at G₂ G₃ G₄ J₂ J₃ J₄
  have e_u := hD.degree_eq_rows hM 0
  have e_a := hD.degree_eq_rows hM 1
  have e_b := hD.degree_eq_rows hM 2
  have r_u := hD.reciprocal_rows_zero hM
  have r_a := hD.reciprocal_rows hM 1 (by decide)
  have r_b := hD.reciprocal_rows hM 2 (by decide)
  simp only [LyonsLabel.rows, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    LyonsRow.toVec, LyonsRow.fourierSum, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue, G₂, G₃, G₄, J₂, J₃,
    J₄, F₂, F₃, F₄, I₂, I₃, I₄, Fq, Fx, Fz, Fp, Iq, Ix, Iz, Ip] at e_u e_a e_b r_u r_a r_b
  push_cast at e_u e_a e_b r_u r_a r_b
  apply lyons_ADG_arithmetic (f χx) (f χq) (f y₁) (f y₂) (f χz)
    (hD.degree_ge y₁ hy₁ hy₁p) (hD.degree_ge y₂ hy₂ hy₂p)
    (hD.modEq_of_row hx hrx (by decide)) (hD.modEq_of_row hy₁ hry₁ (by decide))
    (hD.modEq_of_row hy₂ hry₂ (by decide)) (hD.modEq_of_row hz hrz (by decide))
    (hD.le_of_pos_of_row hq hrq (by decide))
  · exact_mod_cast (by linear_combination e_a - e_u : (8 * f χx + 4 * f χq : ℚ) = 0)
  · have h : (72 : ℚ) / f χx + 400 / f χq = P := by
      simp only [div_eq_mul_inv]
      linear_combination r_a - r_u
    rw [h]
    exact hD.P_pos
  · exact_mod_cast
      (by linear_combination e_a - e_b : (1 + 2 * f χx + f y₁ + f y₂ - f χz : ℚ) = 0)
  · simp only [div_eq_mul_inv]
    linear_combination r_a - r_b

end CFSG.LyonsUnitaryFour
