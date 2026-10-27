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

theorem lyons_signedDegree_ne_J (hD : LyonsSignedDegreeData B row f p N P) :
    B.val.map row ≠ lyonsConfiguration .J := by
  intro hM
  have hcount : ∀ R, (B.val.map row).count R = (lyonsConfiguration .J).count R :=
    fun R => by rw [hM]
  obtain ⟨χh, hh, hrh, huh⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (-2, 2, 1, 1, 1, 1)) (by rw [hcount]; decide)
  obtain ⟨χ1, h1, hr1, hu1⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (-1, 1, 0, 1, 0, 1)) (by rw [hcount]; decide)
  obtain ⟨χ2, h2, hr2, hu2⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (-1, 1, 1, 0, 1, 0)) (by rw [hcount]; decide)
  obtain ⟨ζ1, hz1, hrz1, huz1⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (-1, 1, 1, 2, 1, 2)) (by rw [hcount]; decide)
  obtain ⟨ζ2, hz2, hrz2, huz2⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (-1, 1, 2, 1, 2, 1)) (by rw [hcount]; decide)
  obtain ⟨χw, hw, hrw, huw⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (0, 0, 1, 1, 1, 1)) (by rw [hcount]; decide)
  obtain ⟨v1, hv1, hrv1, huv1⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (1, 1, 0, 1, 2, 1)) (by rw [hcount]; decide)
  obtain ⟨v2, hv2, hrv2, huv2⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (1, 1, 1, 0, 1, 2)) (by rw [hcount]; decide)
  obtain ⟨v3, hv3, hrv3, huv3⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (1, 1, 1, 2, 1, 0)) (by rw [hcount]; decide)
  obtain ⟨v4, hv4, hrv4, huv4⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (1, 1, 2, 1, 0, 1)) (by rw [hcount]; decide)
  obtain ⟨y, hyp, hfibP⟩ := rowFiber_eq_pair_principal hD.principal_mem hD.principal_row
    (by rw [hcount]; decide)
  have hy : y ∈ B ∧ row y = principalRow := mem_rowFiber.mp (by rw [hfibP]; simp)
  obtain ⟨a1, a2, ha12, hfa⟩ := rowFiber_eq_pair (B := B) (row := row) (R := (1, 1, 1, 1, 1, 1))
    (by rw [hcount]; decide)
  obtain ⟨τ, hτ, hτrow⟩ := hD.galois
  have hf2 : f χ2 = f χ1 := degree_rotate_eq τ hτ hτrow h1 (by rw [hr2, hr1]; decide)
    (fun φ hφ e => hu2 φ hφ (e.trans hr2))
  have hfz2 : f ζ2 = f ζ1 := degree_rotate_eq τ hτ hτrow hz1 (by rw [hrz2, hrz1]; decide)
    (fun φ hφ e => huz2 φ hφ (e.trans hrz2))
  have hfv2 : f v2 = f v1 := degree_rotate_eq τ hτ hτrow hv1 (by rw [hrv2, hrv1]; decide)
    (fun φ hφ e => huv2 φ hφ (e.trans hrv2))
  have hfv4 : f v4 = f v1 := (degree_rotate_eq τ hτ hτrow hv2 (by rw [hrv4, hrv2]; decide)
    (fun φ hφ e => huv4 φ hφ (e.trans hrv4))).trans hfv2
  have hfv3 : f v3 = f v1 := (degree_rotate_eq τ hτ hτrow hv4 (by rw [hrv3, hrv4]; decide)
    (fun φ hφ e => huv3 φ hφ (e.trans hrv3))).trans hfv4
  have fh := rowFiber_eq_singleton hh hrh huh
  have f1 := rowFiber_eq_singleton h1 hr1 hu1
  have f2 := rowFiber_eq_singleton h2 hr2 hu2
  have fz1 := rowFiber_eq_singleton hz1 hrz1 huz1
  have fz2 := rowFiber_eq_singleton hz2 hrz2 huz2
  have fw := rowFiber_eq_singleton hw hrw huw
  have fv1 := rowFiber_eq_singleton hv1 hrv1 huv1
  have fv2 := rowFiber_eq_singleton hv2 hrv2 huv2
  have fv3 := rowFiber_eq_singleton hv3 hrv3 huv3
  have fv4 := rowFiber_eq_singleton hv4 hrv4 huv4
  have hpy : p ∉ ({y} : Finset ι) := by simpa using fun h => hyp h.symm
  have expand : ∀ (G : LyonsRow → ℚ) (H : ι → ℚ), ∑ χ ∈ B, G (row χ) * H χ =
      G (-2, 2, 1, 1, 1, 1) * H χh + G (-1, 1, 0, 1, 0, 1) * H χ1 +
        G (-1, 1, 1, 0, 1, 0) * H χ2 + G (-1, 1, 1, 2, 1, 2) * H ζ1 +
        G (-1, 1, 2, 1, 2, 1) * H ζ2 + G (0, 0, 1, 1, 1, 1) * H χw +
        G (1, 1, 0, 0, 0, 0) * (H p + H y) + G (1, 1, 0, 1, 2, 1) * H v1 +
        G (1, 1, 1, 0, 1, 2) * H v2 + G (1, 1, 1, 1, 1, 1) * (H a1 + H a2) +
        G (1, 1, 1, 2, 1, 0) * H v3 + G (1, 1, 2, 1, 0, 1) * H v4 := by
    intro G H
    rw [sum_mul_row_eq hM G H]
    simp only [LyonsLabel.rows, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]
    rw [fh, f1, f2, fz1, fz2, fw, show ((1, 1, 0, 0, 0, 0) : LyonsRow) = principalRow from rfl,
      hfibP, fv1, fv2, hfa, fv3, fv4, Finset.sum_insert hpy, Finset.sum_pair ha12]
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
    hfp, hf2, hfz2, hfv2, hfv3, hfv4] at e_u e_a e_b r_u r_a r_b
  norm_num at e_u e_a e_b r_u r_a r_b
  have cx : f χ1 ≡ 51 [ZMOD 64] := by
    have := hD.residue h1 hr1
    simp only [LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have cz : f ζ1 ≡ 39 [ZMOD 64] := by
    have := hD.residue hz1 hrz1
    simp only [LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have ch : f χh ≡ 38 [ZMOD 64] := by
    have := hD.residue hh hrh
    simp only [LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have cy : f y ≡ 1 [ZMOD 64] := by
    have := hD.residue hy.1 hy.2
    simp only [principalRow, LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have cw : f χw ≡ 52 [ZMOD 64] := by
    have := hD.residue hw hrw
    simp only [LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have ph : 0 < f χh → 102 ≤ f χh := fun hpos => by
    have := hD.pos_bound hh hrh hpos
    simp only [LyonsRow.fourierSum] at this
    omega
  have hy12 : 12 ≤ |f y| := hD.degree_ge y hy.1 hyp
  have hyuniq : ∀ ψ ∈ B, row ψ = row y → f ψ = f y → ψ = y := by
    intro ψ hψ hrow hf
    have hψP : ψ ∈ rowFiber B row principalRow := mem_rowFiber.mpr ⟨hψ, hrow.trans hy.2⟩
    rw [hfibP, Finset.mem_insert, Finset.mem_singleton] at hψP
    rcases hψP with rfl | h
    · exfalso
      rw [hD.principal_degree] at hf
      rw [← hf] at hy12
      norm_num at hy12
    · exact h
  have hp1 := hD.prime_le_of_unique h1 (hD.ne_principal hr1 (by decide))
    (unique_degree_of_unique_row hr1 hu1)
  have hpz := hD.prime_le_of_unique hz1 (hD.ne_principal hrz1 (by decide))
    (unique_degree_of_unique_row hrz1 huz1)
  have hph := hD.prime_le_of_unique hh (hD.ne_principal hrh (by decide))
    (unique_degree_of_unique_row hrh huh)
  have hpy' := hD.prime_le_of_unique hy.1 hyp hyuniq
  have hpw := hD.prime_le_of_unique hw (hD.ne_principal hrw (by decide))
    (unique_degree_of_unique_row hrw huw)
  apply lyons_J_arithmetic (f χ1) (f ζ1) (f χh) (f y) (f χw) hy12 cx cz ch cy cw ph
  · intro q hqp hdvd
    rcases hdvd with hdvd | hdvd
    · exact ⟨hp1 χ1 h1 q hqp hdvd, hpz χ1 h1 q hqp hdvd, hph χ1 h1 q hqp hdvd,
        hpy' χ1 h1 q hqp hdvd, hpw χ1 h1 q hqp hdvd⟩
    · exact ⟨hp1 ζ1 hz1 q hqp hdvd, hpz ζ1 hz1 q hqp hdvd, hph ζ1 hz1 q hqp hdvd,
        hpy' ζ1 hz1 q hqp hdvd, hpw ζ1 hz1 q hqp hdvd⟩
  · simp only [div_eq_mul_inv]
    linear_combination r_a - r_b
  · have : (1 + f χ1 - f ζ1 + f χh + f y - f χw : ℚ) = 0 := by linear_combination e_a - e_b
    exact_mod_cast this
  · have : (f χ1 + f ζ1 + f χh : ℚ) = 0 := by linear_combination (e_a - e_u) / 4
    exact_mod_cast this
  · have : -(4 : ℚ) + 392 / f ζ1 - 4 / f y + 64 / f χw = P := by
      simp only [div_eq_mul_inv]
      linear_combination -3 * r_a + 4 * r_b - r_u
    rw [this]
    exact hD.P_pos

end CFSG.LyonsUnitaryFour
