module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Exclusions.SignedDegreeTools
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Enumeration.ExclusionArithmeticPrime
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

open scoped BigOperators

namespace CFSG.LyonsUnitaryFour

variable {ι : Type*} [DecidableEq ι] {B : Finset ι} {row : ι → LyonsRow} {f : ι → ℤ} {p : ι}
  {N : ℕ} {P : ℚ}

theorem lyons_signedDegree_ne_B1 (hD : LyonsSignedDegreeData B row f p N P) :
    B.val.map row ≠ lyonsConfiguration .B1 := by
  intro hM
  have hcount : ∀ R, (B.val.map row).count R = (lyonsConfiguration .B1).count R :=
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
  obtain ⟨χw, hw, hrw, huw⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (0, 0, 1, 1, 1, 1)) (by rw [hcount]; decide)
  obtain ⟨χp, hp', hrp, hup⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := principalRow) (by rw [hcount]; decide)
  obtain ⟨χz, hz, hrz, huz⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (1, 1, 2, 2, 2, 2)) (by rw [hcount]; decide)
  obtain ⟨χh, hh, hrh, huh⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (2, 2, 1, 1, 1, 1)) (by rw [hcount]; decide)
  obtain ⟨a1, a2, ha12, hfa⟩ := rowFiber_eq_pair (B := B) (row := row) (R := (1, 1, 1, 1, 1, 1))
    (by rw [hcount]; decide)
  have ha1 : a1 ∈ B ∧ row a1 = (1, 1, 1, 1, 1, 1) := mem_rowFiber.mp (by rw [hfa]; simp)
  have ha2 : a2 ∈ B ∧ row a2 = (1, 1, 1, 1, 1, 1) := mem_rowFiber.mp (by rw [hfa]; simp)
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
  have fw := rowFiber_eq_singleton hw hrw huw
  have fz := rowFiber_eq_singleton hz hrz huz
  have fh := rowFiber_eq_singleton hh hrh huh
  have fp : rowFiber B row principalRow = {p} :=
    rowFiber_eq_singleton hD.principal_mem hD.principal_row fun ψ hψ e =>
      (hup ψ hψ e).trans (hup p hD.principal_mem hD.principal_row).symm
  have expand : ∀ (G : LyonsRow → ℚ) (H : ι → ℚ), ∑ χ ∈ B, G (row χ) * H χ =
      G (-2, 2, 2, 2, 2, 2) * H χq + G (-1, 1, -1, 1, 1, 1) * H χ1 +
        G (-1, 1, 1, -1, 1, 1) * H χ2 + G (-1, 1, 1, 1, -1, 1) * H χ3 +
        G (-1, 1, 1, 1, 1, -1) * H χ4 + G (0, 0, 1, 1, 1, 1) * H χw +
        G (1, 1, 0, 0, 0, 0) * H p + G (1, 1, 1, 1, 1, 1) * (H a1 + H a2) +
        G (1, 1, 2, 2, 2, 2) * H χz + G (2, 2, 1, 1, 1, 1) * H χh := by
    intro G H
    rw [sum_mul_row_eq hM G H]
    simp only [LyonsLabel.rows, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]
    rw [fq, f1, f2, f3, f4, fw, show ((1, 1, 0, 0, 0, 0) : LyonsRow) = principalRow from rfl,
      fp, hfa, fz, fh, Finset.sum_pair ha12]
    simp only [Finset.sum_singleton]
    ring
  have hfp : (f p : ℚ) = 1 := by rw [hD.principal_degree]; simp
  have e_u := hD.degree_sum_rat 0
  have e_a := hD.degree_sum_rat 1
  have e_b := hD.degree_sum_rat 2
  rw [expand (fun R => ((R.toVec 0 : ℤ) : ℚ)) (fun χ => (f χ : ℚ))] at e_u
  rw [expand (fun R => ((R.toVec 1 : ℤ) : ℚ)) (fun χ => (f χ : ℚ))] at e_a
  rw [expand (fun R => ((R.toVec 2 : ℤ) : ℚ)) (fun χ => (f χ : ℚ))] at e_b
  have r_u := hD.reciprocal_sum 0
  have r_a := hD.reciprocal_sum 1
  have r_b := hD.reciprocal_sum 2
  rw [expand (fun R => ((R.fourierSum : ℚ) ^ 2 * (R.toVec 0 : ℚ)))
    (fun χ => ((f χ : ℚ))⁻¹)] at r_u
  rw [expand (fun R => ((R.fourierSum : ℚ) ^ 2 * (R.toVec 1 : ℚ)))
    (fun χ => ((f χ : ℚ))⁻¹)] at r_a
  rw [expand (fun R => ((R.fourierSum : ℚ) ^ 2 * (R.toVec 2 : ℚ)))
    (fun χ => ((f χ : ℚ))⁻¹)] at r_b
  simp only [LyonsRow.toVec, LyonsRow.fourierSum, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Fin.isValue, Int.cast_neg, Int.cast_one, Int.cast_ofNat, Int.cast_zero,
    hfp, hf2, hf3, hf4] at e_u e_a e_b r_u r_a r_b
  norm_num at e_u e_a e_b r_u r_a r_b
  have cx : f χ1 ≡ 51 [ZMOD 64] := by
    have := hD.residue h1 hr1
    simp only [LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have ca₁ : f a1 ≡ 53 [ZMOD 64] := by
    have := hD.residue ha1.1 ha1.2
    simp only [LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have ca₂ : f a2 ≡ 53 [ZMOD 64] := by
    have := hD.residue ha2.1 ha2.2
    simp only [LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have cz : f χz ≡ 41 [ZMOD 64] := by
    have := hD.residue hz hrz
    simp only [LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have ch : f χh ≡ 54 [ZMOD 64] := by
    have := hD.residue hh hrh
    simp only [LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have cw : f χw ≡ 52 [ZMOD 64] := by
    have := hD.residue hw hrw
    simp only [LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have hq90 : 0 < f χq → 90 ≤ f χq := fun hpos => by
    have := hD.pos_bound hq hrq hpos
    simp only [LyonsRow.fourierSum] at this
    omega
  have na₁ : f a1 < 0 → f a1 ≤ -75 := fun hneg => by
    have := hD.neg_bound ha1.1 ha1.2 hneg
    simp only [LyonsRow.fourierSum] at this
    omega
  have na₂ : f a2 < 0 → f a2 ≤ -75 := fun hneg => by
    have := hD.neg_bound ha2.1 ha2.2 hneg
    simp only [LyonsRow.fourierSum] at this
    omega
  have nh : f χh < 0 → f χh ≤ -138 := fun hneg => by
    have := hD.neg_bound hh hrh hneg
    simp only [LyonsRow.fourierSum] at this
    omega
  have hp1 := hD.prime_le_of_unique h1 (hD.ne_principal hr1 (by decide))
    (unique_degree_of_unique_row hr1 hu1)
  have hpw := hD.prime_le_of_unique hw (hD.ne_principal hrw (by decide))
    (unique_degree_of_unique_row hrw huw)
  apply lyons_B_arithmetic (f χ1) (f χq) (f a1) (f a2) (f χz) (f χh) (f χw) cx ca₁ ca₂ cz ch cw
    hq90 na₁ na₂ nh
  · intro q hqp hdvd
    rcases hdvd with hdvd | hdvd
    · exact ⟨hp1 χz hz q hqp hdvd, hpw χz hz q hqp hdvd⟩
    · exact ⟨hp1 χh hh q hqp hdvd, hpw χh hh q hqp hdvd⟩
  · have : (8 * f χ1 + 4 * f χq : ℚ) = 0 := by linear_combination e_a - e_u
    exact_mod_cast this
  · have : (72 : ℚ) / f χ1 + 400 / f χq = P := by
      simp only [div_eq_mul_inv]
      linear_combination r_a - r_u
    rw [this]
    exact hD.P_pos
  · simp only [div_eq_mul_inv]
    linear_combination r_a - r_b
  · simp only [div_eq_mul_inv]
    linear_combination r_a - r_b + r_u
  · have : (1 + 2 * f χ1 - f χz + f χh - f χw : ℚ) = 0 := by linear_combination e_a - e_b
    exact_mod_cast this
  · have : (1 - 4 * f χ1 - 2 * f χq + f a1 + f a2 + f χz + 2 * f χh : ℚ) = 0 := by
      linear_combination e_u
    exact_mod_cast this

theorem lyons_signedDegree_ne_B2 (hD : LyonsSignedDegreeData B row f p N P) :
    B.val.map row ≠ lyonsConfiguration .B2 := by
  intro hM
  have hcount : ∀ R, (B.val.map row).count R = (lyonsConfiguration .B2).count R :=
    fun R => by rw [hM]
  obtain ⟨χq, hq, hrq, huq⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (-2, 2, 2, 2, 2, 2)) (by rw [hcount]; decide)
  obtain ⟨χ1, h1, hr1, hu1⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (-1, 1, 0, 0, 0, 2)) (by rw [hcount]; decide)
  obtain ⟨χ2, h2, hr2, hu2⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (-1, 1, 0, 0, 2, 0)) (by rw [hcount]; decide)
  obtain ⟨χ3, h3, hr3, hu3⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (-1, 1, 0, 2, 0, 0)) (by rw [hcount]; decide)
  obtain ⟨χ4, h4, hr4, hu4⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (-1, 1, 2, 0, 0, 0)) (by rw [hcount]; decide)
  obtain ⟨χw, hw, hrw, huw⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (0, 0, 1, 1, 1, 1)) (by rw [hcount]; decide)
  obtain ⟨χp, hp', hrp, hup⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := principalRow) (by rw [hcount]; decide)
  obtain ⟨χz, hz, hrz, huz⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (1, 1, 2, 2, 2, 2)) (by rw [hcount]; decide)
  obtain ⟨χh, hh, hrh, huh⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (2, 2, 1, 1, 1, 1)) (by rw [hcount]; decide)
  obtain ⟨a1, a2, ha12, hfa⟩ := rowFiber_eq_pair (B := B) (row := row) (R := (1, 1, 1, 1, 1, 1))
    (by rw [hcount]; decide)
  have ha1 : a1 ∈ B ∧ row a1 = (1, 1, 1, 1, 1, 1) := mem_rowFiber.mp (by rw [hfa]; simp)
  have ha2 : a2 ∈ B ∧ row a2 = (1, 1, 1, 1, 1, 1) := mem_rowFiber.mp (by rw [hfa]; simp)
  obtain ⟨τ, hτ, hτrow⟩ := hD.galois
  have hf4 : f χ4 = f χ1 := degree_rotate_eq τ hτ hτrow h1 (by rw [hr4, hr1]; decide)
    (fun φ hφ e => hu4 φ hφ (e.trans hr4))
  have hf3 : f χ3 = f χ1 := (degree_rotate_eq τ hτ hτrow h4 (by rw [hr3, hr4]; decide)
    (fun φ hφ e => hu3 φ hφ (e.trans hr3))).trans hf4
  have hf2 : f χ2 = f χ1 := (degree_rotate_eq τ hτ hτrow h3 (by rw [hr2, hr3]; decide)
    (fun φ hφ e => hu2 φ hφ (e.trans hr2))).trans hf3
  have fq := rowFiber_eq_singleton hq hrq huq
  have f1 := rowFiber_eq_singleton h1 hr1 hu1
  have f2 := rowFiber_eq_singleton h2 hr2 hu2
  have f3 := rowFiber_eq_singleton h3 hr3 hu3
  have f4 := rowFiber_eq_singleton h4 hr4 hu4
  have fw := rowFiber_eq_singleton hw hrw huw
  have fz := rowFiber_eq_singleton hz hrz huz
  have fh := rowFiber_eq_singleton hh hrh huh
  have fp : rowFiber B row principalRow = {p} :=
    rowFiber_eq_singleton hD.principal_mem hD.principal_row fun ψ hψ e =>
      (hup ψ hψ e).trans (hup p hD.principal_mem hD.principal_row).symm
  have expand : ∀ (G : LyonsRow → ℚ) (H : ι → ℚ), ∑ χ ∈ B, G (row χ) * H χ =
      G (-2, 2, 2, 2, 2, 2) * H χq + G (-1, 1, 0, 0, 0, 2) * H χ1 +
        G (-1, 1, 0, 0, 2, 0) * H χ2 + G (-1, 1, 0, 2, 0, 0) * H χ3 +
        G (-1, 1, 2, 0, 0, 0) * H χ4 + G (0, 0, 1, 1, 1, 1) * H χw +
        G (1, 1, 0, 0, 0, 0) * H p + G (1, 1, 1, 1, 1, 1) * (H a1 + H a2) +
        G (1, 1, 2, 2, 2, 2) * H χz + G (2, 2, 1, 1, 1, 1) * H χh := by
    intro G H
    rw [sum_mul_row_eq hM G H]
    simp only [LyonsLabel.rows, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]
    rw [fq, f1, f2, f3, f4, fw, show ((1, 1, 0, 0, 0, 0) : LyonsRow) = principalRow from rfl,
      fp, hfa, fz, fh, Finset.sum_pair ha12]
    simp only [Finset.sum_singleton]
    ring
  have hfp : (f p : ℚ) = 1 := by rw [hD.principal_degree]; simp
  have e_u := hD.degree_sum_rat 0
  have e_a := hD.degree_sum_rat 1
  have e_b := hD.degree_sum_rat 2
  rw [expand (fun R => ((R.toVec 0 : ℤ) : ℚ)) (fun χ => (f χ : ℚ))] at e_u
  rw [expand (fun R => ((R.toVec 1 : ℤ) : ℚ)) (fun χ => (f χ : ℚ))] at e_a
  rw [expand (fun R => ((R.toVec 2 : ℤ) : ℚ)) (fun χ => (f χ : ℚ))] at e_b
  have r_u := hD.reciprocal_sum 0
  have r_a := hD.reciprocal_sum 1
  have r_b := hD.reciprocal_sum 2
  rw [expand (fun R => ((R.fourierSum : ℚ) ^ 2 * (R.toVec 0 : ℚ)))
    (fun χ => ((f χ : ℚ))⁻¹)] at r_u
  rw [expand (fun R => ((R.fourierSum : ℚ) ^ 2 * (R.toVec 1 : ℚ)))
    (fun χ => ((f χ : ℚ))⁻¹)] at r_a
  rw [expand (fun R => ((R.fourierSum : ℚ) ^ 2 * (R.toVec 2 : ℚ)))
    (fun χ => ((f χ : ℚ))⁻¹)] at r_b
  simp only [LyonsRow.toVec, LyonsRow.fourierSum, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Fin.isValue, Int.cast_neg, Int.cast_one, Int.cast_ofNat, Int.cast_zero,
    hfp, hf2, hf3, hf4] at e_u e_a e_b r_u r_a r_b
  norm_num at e_u e_a e_b r_u r_a r_b
  have cx : f χ1 ≡ 51 [ZMOD 64] := by
    have := hD.residue h1 hr1
    simp only [LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have ca₁ : f a1 ≡ 53 [ZMOD 64] := by
    have := hD.residue ha1.1 ha1.2
    simp only [LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have ca₂ : f a2 ≡ 53 [ZMOD 64] := by
    have := hD.residue ha2.1 ha2.2
    simp only [LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have cz : f χz ≡ 41 [ZMOD 64] := by
    have := hD.residue hz hrz
    simp only [LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have ch : f χh ≡ 54 [ZMOD 64] := by
    have := hD.residue hh hrh
    simp only [LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have cw : f χw ≡ 52 [ZMOD 64] := by
    have := hD.residue hw hrw
    simp only [LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have hq90 : 0 < f χq → 90 ≤ f χq := fun hpos => by
    have := hD.pos_bound hq hrq hpos
    simp only [LyonsRow.fourierSum] at this
    omega
  have na₁ : f a1 < 0 → f a1 ≤ -75 := fun hneg => by
    have := hD.neg_bound ha1.1 ha1.2 hneg
    simp only [LyonsRow.fourierSum] at this
    omega
  have na₂ : f a2 < 0 → f a2 ≤ -75 := fun hneg => by
    have := hD.neg_bound ha2.1 ha2.2 hneg
    simp only [LyonsRow.fourierSum] at this
    omega
  have nh : f χh < 0 → f χh ≤ -138 := fun hneg => by
    have := hD.neg_bound hh hrh hneg
    simp only [LyonsRow.fourierSum] at this
    omega
  have hp1 := hD.prime_le_of_unique h1 (hD.ne_principal hr1 (by decide))
    (unique_degree_of_unique_row hr1 hu1)
  have hpw := hD.prime_le_of_unique hw (hD.ne_principal hrw (by decide))
    (unique_degree_of_unique_row hrw huw)
  apply lyons_B_arithmetic (f χ1) (f χq) (f a1) (f a2) (f χz) (f χh) (f χw) cx ca₁ ca₂ cz ch cw
    hq90 na₁ na₂ nh
  · intro q hqp hdvd
    rcases hdvd with hdvd | hdvd
    · exact ⟨hp1 χz hz q hqp hdvd, hpw χz hz q hqp hdvd⟩
    · exact ⟨hp1 χh hh q hqp hdvd, hpw χh hh q hqp hdvd⟩
  · have : (8 * f χ1 + 4 * f χq : ℚ) = 0 := by linear_combination e_a - e_u
    exact_mod_cast this
  · have : (72 : ℚ) / f χ1 + 400 / f χq = P := by
      simp only [div_eq_mul_inv]
      linear_combination r_a - r_u
    rw [this]
    exact hD.P_pos
  · simp only [div_eq_mul_inv]
    linear_combination r_a - r_b
  · simp only [div_eq_mul_inv]
    linear_combination r_a - r_b + r_u
  · have : (1 + 2 * f χ1 - f χz + f χh - f χw : ℚ) = 0 := by linear_combination e_a - e_b
    exact_mod_cast this
  · have : (1 - 4 * f χ1 - 2 * f χq + f a1 + f a2 + f χz + 2 * f χh : ℚ) = 0 := by
      linear_combination e_u
    exact_mod_cast this

end CFSG.LyonsUnitaryFour
