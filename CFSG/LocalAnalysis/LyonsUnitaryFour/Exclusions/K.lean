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

theorem lyons_signedDegree_ne_K (hD : LyonsSignedDegreeData B row f p N P) :
    B.val.map row ≠ lyonsConfiguration .K := by
  intro hM
  have hcount : ∀ R, (B.val.map row).count R = (lyonsConfiguration .K).count R :=
    fun R => by rw [hM]
  obtain ⟨χq, hq, hrq, huq⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (-2, 2, 2, 2, 2, 2)) (by rw [hcount]; decide)
  obtain ⟨c1, c2, hc12, hfc⟩ := rowFiber_eq_pair (B := B) (row := row) (R := (-1, 1, 0, 1, 0, 1))
    (by rw [hcount]; decide)
  obtain ⟨c3, c4, hc34, hfc'⟩ := rowFiber_eq_pair (B := B) (row := row)
    (R := (-1, 1, 1, 0, 1, 0)) (by rw [hcount]; decide)
  obtain ⟨y1, y2, hy1p, hy2p, hy12, hfibP⟩ := rowFiber_eq_triple hD.principal_mem
    hD.principal_row (by rw [hcount]; decide)
  obtain ⟨v1, hv1, hrv1, huv1⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (1, 1, 0, 1, 2, 1)) (by rw [hcount]; decide)
  obtain ⟨v2, hv2, hrv2, huv2⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (1, 1, 1, 0, 1, 2)) (by rw [hcount]; decide)
  obtain ⟨v3, hv3, hrv3, huv3⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (1, 1, 1, 2, 1, 0)) (by rw [hcount]; decide)
  obtain ⟨v4, hv4, hrv4, huv4⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (1, 1, 2, 1, 0, 1)) (by rw [hcount]; decide)
  obtain ⟨χz, hz, hrz, huz⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (1, 1, 2, 2, 2, 2)) (by rw [hcount]; decide)
  have hc1 : c1 ∈ B ∧ row c1 = (-1, 1, 0, 1, 0, 1) := mem_rowFiber.mp (by rw [hfc]; simp)
  have hc2 : c2 ∈ B ∧ row c2 = (-1, 1, 0, 1, 0, 1) := mem_rowFiber.mp (by rw [hfc]; simp)
  have hy1 : y1 ∈ B ∧ row y1 = principalRow := mem_rowFiber.mp (by rw [hfibP]; simp)
  have hy2 : y2 ∈ B ∧ row y2 = principalRow := mem_rowFiber.mp (by rw [hfibP]; simp)
  obtain ⟨τ, hτ, hτrow⟩ := hD.galois
  have hrot : ∀ g : ℤ → ℚ, g (f c3) + g (f c4) = g (f c1) + g (f c2) := by
    intro g
    have h := sum_rowFiber_rotate τ hτ hτrow (-1, 1, 0, 1, 0, 1) g
    rw [show LyonsRow.rotate (-1, 1, 0, 1, 0, 1) = (-1, 1, 1, 0, 1, 0) from rfl, hfc', hfc,
      Finset.sum_pair hc34, Finset.sum_pair hc12] at h
    exact h
  have hsum3 : (f c3 : ℚ) + f c4 = f c1 + f c2 := hrot fun n => (n : ℚ)
  have hinv3 : ((f c3 : ℚ))⁻¹ + ((f c4 : ℚ))⁻¹ = ((f c1 : ℚ))⁻¹ + ((f c2 : ℚ))⁻¹ :=
    hrot fun n => ((n : ℚ))⁻¹
  have hfv2 : f v2 = f v1 := degree_rotate_eq τ hτ hτrow hv1 (by rw [hrv2, hrv1]; decide)
    (fun φ hφ e => huv2 φ hφ (e.trans hrv2))
  have hfv4 : f v4 = f v1 := (degree_rotate_eq τ hτ hτrow hv2 (by rw [hrv4, hrv2]; decide)
    (fun φ hφ e => huv4 φ hφ (e.trans hrv4))).trans hfv2
  have hfv3 : f v3 = f v1 := (degree_rotate_eq τ hτ hτrow hv4 (by rw [hrv3, hrv4]; decide)
    (fun φ hφ e => huv3 φ hφ (e.trans hrv3))).trans hfv4
  have fq := rowFiber_eq_singleton hq hrq huq
  have fv1 := rowFiber_eq_singleton hv1 hrv1 huv1
  have fv2 := rowFiber_eq_singleton hv2 hrv2 huv2
  have fv3 := rowFiber_eq_singleton hv3 hrv3 huv3
  have fv4 := rowFiber_eq_singleton hv4 hrv4 huv4
  have fz := rowFiber_eq_singleton hz hrz huz
  have hpy : p ∉ ({y1, y2} : Finset ι) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hy1p h.symm, fun h => hy2p h.symm⟩
  have expand : ∀ (G : LyonsRow → ℚ) (H : ι → ℚ), ∑ χ ∈ B, G (row χ) * H χ =
      G (-2, 2, 2, 2, 2, 2) * H χq + G (-1, 1, 0, 1, 0, 1) * (H c1 + H c2) +
        G (-1, 1, 1, 0, 1, 0) * (H c3 + H c4) + G (1, 1, 0, 0, 0, 0) * (H p + (H y1 + H y2)) +
        G (1, 1, 0, 1, 2, 1) * H v1 + G (1, 1, 1, 0, 1, 2) * H v2 +
        G (1, 1, 1, 2, 1, 0) * H v3 + G (1, 1, 2, 1, 0, 1) * H v4 +
        G (1, 1, 2, 2, 2, 2) * H χz := by
    intro G H
    rw [sum_mul_row_eq hM G H]
    simp only [LyonsLabel.rows, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]
    rw [fq, hfc, hfc', show ((1, 1, 0, 0, 0, 0) : LyonsRow) = principalRow from rfl, hfibP, fv1,
      fv2, fv3, fv4, fz, Finset.sum_pair hc12, Finset.sum_pair hc34, Finset.sum_insert hpy,
      Finset.sum_pair hy12]
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
    Matrix.cons_val_two, Fin.isValue, Int.cast_neg, Int.cast_one, Int.cast_ofNat, hfp, hfv2,
    hfv3, hfv4] at e_u e_a e_b r_u r_a r_b
  norm_num at e_u e_a e_b r_u r_a r_b
  have c₁ : f c1 ≡ 51 [ZMOD 64] := by
    have := hD.residue hc1.1 hc1.2
    simp only [LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have c₂ : f c2 ≡ 51 [ZMOD 64] := by
    have := hD.residue hc2.1 hc2.2
    simp only [LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have cz : f χz ≡ 41 [ZMOD 64] := by
    have := hD.residue hz hrz
    simp only [LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have d₁ : f y1 ≡ 1 [ZMOD 64] := by
    have := hD.residue hy1.1 hy1.2
    simp only [principalRow, LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have d₂ : f y2 ≡ 1 [ZMOD 64] := by
    have := hD.residue hy2.1 hy2.2
    simp only [principalRow, LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have hq90 : 0 < f χq → 90 ≤ f χq := fun hpos => by
    have := hD.pos_bound hq hrq hpos
    simp only [LyonsRow.fourierSum] at this
    omega
  have hy₁ : 12 ≤ |f y1| := hD.degree_ge y1 hy1.1 hy1p
  have hy₂ : 12 ≤ |f y2| := hD.degree_ge y2 hy2.1 hy2p
  apply lyons_K_arithmetic (f c1) (f c2) (f χq) (f χz) (f y1) (f y2) hy₁ hy₂ c₁ c₂ cz d₁ d₂ hq90
  · intro hne q hqp hdvd
    have hc1p : c1 ≠ p := hD.ne_principal hc1.2 (by decide)
    have hc2p : c2 ≠ p := hD.ne_principal hc2.2 (by decide)
    have hfc21 : rowFiber B row (-1, 1, 0, 1, 0, 1) = {c2, c1} := by
      rw [hfc, Finset.pair_comm]
    have hp1 := hD.prime_le_of_unique hc1.1 hc1p (unique_degree_of_pair hfc hne)
    have hp2 := hD.prime_le_of_unique hc2.1 hc2p (unique_degree_of_pair hfc21 (Ne.symm hne))
    rcases hdvd with hdvd | hdvd | hdvd | hdvd | hdvd
    · exact ⟨hp1 c1 hc1.1 q hqp hdvd, hp2 c1 hc1.1 q hqp hdvd⟩
    · exact ⟨hp1 c2 hc2.1 q hqp hdvd, hp2 c2 hc2.1 q hqp hdvd⟩
    · exact ⟨hp1 χz hz q hqp hdvd, hp2 χz hz q hqp hdvd⟩
    · exact ⟨hp1 y1 hy1.1 q hqp hdvd, hp2 y1 hy1.1 q hqp hdvd⟩
    · exact ⟨hp1 y2 hy2.1 q hqp hdvd, hp2 y2 hy2.1 q hqp hdvd⟩
  · simp only [div_eq_mul_inv]
    linear_combination r_a - r_b
  · have : (1 + f c1 + f c2 - f χz + f y1 + f y2 : ℚ) = 0 := by linear_combination e_a - e_b
    exact_mod_cast this
  · have : (f χq : ℚ) = -(f c1 + f c2) := by linear_combination (e_a - e_u - 2 * hsum3) / 4
    exact_mod_cast this
  · have : (36 : ℚ) / f c1 + 36 / f c2 + 400 / f χq = P := by
      simp only [div_eq_mul_inv]
      linear_combination r_a - r_u - 18 * hinv3
    rw [this]
    exact hD.P_pos

end CFSG.LyonsUnitaryFour
