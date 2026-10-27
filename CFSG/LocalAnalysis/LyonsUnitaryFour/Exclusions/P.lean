module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Exclusions.SignedDegreeTools
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Enumeration.NumericalP
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

open scoped BigOperators

namespace CFSG.LyonsUnitaryFour

variable {ι : Type*} [DecidableEq ι] {B : Finset ι} {row : ι → LyonsRow} {f : ι → ℤ} {p : ι}
  {N : ℕ} {P : ℚ}

theorem lyons_signedDegree_ne_P (hD : LyonsSignedDegreeData B row f p N P) :
    B.val.map row ≠ lyonsConfiguration .P := by
  intro hM
  have hcount : ∀ R, (B.val.map row).count R = (lyonsConfiguration .P).count R :=
    fun R => by rw [hM]
  obtain ⟨χ5, h5, hr5, hu5⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (-2, 2, 2, 2, 2, 2)) (by rw [hcount]; decide)
  obtain ⟨χ9, χ10, h910, hf9⟩ := rowFiber_eq_pair (B := B) (row := row)
    (R := (0, 0, 1, 1, 1, 1)) (by rw [hcount]; decide)
  obtain ⟨χ3, χ4, h34, hf3⟩ := rowFiber_eq_pair (B := B) (row := row) (R := (0, 1, 0, 1, 1, 1))
    (by rw [hcount]; decide)
  obtain ⟨χ1, χ2, h12, hf1⟩ := rowFiber_eq_pair (B := B) (row := row) (R := (1, 0, 0, 0, 0, 1))
    (by rw [hcount]; decide)
  obtain ⟨χ6, h6p, hfibP⟩ := rowFiber_eq_pair_principal hD.principal_mem hD.principal_row
    (by rw [hcount]; decide)
  obtain ⟨χ7, χ8, h78, hf7⟩ := rowFiber_eq_pair (B := B) (row := row) (R := (1, 1, 1, 1, 1, 1))
    (by rw [hcount]; decide)
  have m1 : χ1 ∈ B ∧ row χ1 = (1, 0, 0, 0, 0, 1) := mem_rowFiber.mp (by rw [hf1]; simp)
  have m2 : χ2 ∈ B ∧ row χ2 = (1, 0, 0, 0, 0, 1) := mem_rowFiber.mp (by rw [hf1]; simp)
  have m3 : χ3 ∈ B ∧ row χ3 = (0, 1, 0, 1, 1, 1) := mem_rowFiber.mp (by rw [hf3]; simp)
  have m4 : χ4 ∈ B ∧ row χ4 = (0, 1, 0, 1, 1, 1) := mem_rowFiber.mp (by rw [hf3]; simp)
  have m6 : χ6 ∈ B ∧ row χ6 = principalRow := mem_rowFiber.mp (by rw [hfibP]; simp)
  have m7 : χ7 ∈ B ∧ row χ7 = (1, 1, 1, 1, 1, 1) := mem_rowFiber.mp (by rw [hf7]; simp)
  have m8 : χ8 ∈ B ∧ row χ8 = (1, 1, 1, 1, 1, 1) := mem_rowFiber.mp (by rw [hf7]; simp)
  have m9 : χ9 ∈ B ∧ row χ9 = (0, 0, 1, 1, 1, 1) := mem_rowFiber.mp (by rw [hf9]; simp)
  have m10 : χ10 ∈ B ∧ row χ10 = (0, 0, 1, 1, 1, 1) := mem_rowFiber.mp (by rw [hf9]; simp)
  obtain ⟨τ, hτ, hτrow⟩ := hD.galois
  have rot : ∀ (R : LyonsRow) (g : ℤ → ℚ),
      ∑ ψ ∈ rowFiber B row R.rotate, g (f ψ) = ∑ χ ∈ rowFiber B row R, g (f χ) :=
    fun R g => sum_rowFiber_rotate τ hτ hτrow R g
  have rh1 : ∀ g : ℤ → ℚ, ∑ ψ ∈ rowFiber B row (0, 1, 1, 0, 1, 1), g (f ψ) =
      ∑ χ ∈ rowFiber B row (0, 1, 0, 1, 1, 1), g (f χ) := fun g => rot (0, 1, 0, 1, 1, 1) g
  have rh2 : ∀ g : ℤ → ℚ, ∑ ψ ∈ rowFiber B row (0, 1, 1, 1, 0, 1), g (f ψ) =
      ∑ χ ∈ rowFiber B row (0, 1, 0, 1, 1, 1), g (f χ) := fun g =>
    (rot (0, 1, 1, 0, 1, 1) g).trans (rh1 g)
  have rh3 : ∀ g : ℤ → ℚ, ∑ ψ ∈ rowFiber B row (0, 1, 1, 1, 1, 0), g (f ψ) =
      ∑ χ ∈ rowFiber B row (0, 1, 0, 1, 1, 1), g (f χ) := fun g =>
    (rot (0, 1, 1, 1, 0, 1) g).trans (rh2 g)
  have rx1 : ∀ g : ℤ → ℚ, ∑ ψ ∈ rowFiber B row (1, 0, 1, 0, 0, 0), g (f ψ) =
      ∑ χ ∈ rowFiber B row (1, 0, 0, 0, 0, 1), g (f χ) := fun g => rot (1, 0, 0, 0, 0, 1) g
  have rx2 : ∀ g : ℤ → ℚ, ∑ ψ ∈ rowFiber B row (1, 0, 0, 1, 0, 0), g (f ψ) =
      ∑ χ ∈ rowFiber B row (1, 0, 0, 0, 0, 1), g (f χ) := fun g =>
    (rot (1, 0, 1, 0, 0, 0) g).trans (rx1 g)
  have rx3 : ∀ g : ℤ → ℚ, ∑ ψ ∈ rowFiber B row (1, 0, 0, 0, 1, 0), g (f ψ) =
      ∑ χ ∈ rowFiber B row (1, 0, 0, 0, 0, 1), g (f χ) := fun g =>
    (rot (1, 0, 0, 1, 0, 0) g).trans (rx2 g)
  have f5 := rowFiber_eq_singleton h5 hr5 hu5
  have hp6 : p ∉ ({χ6} : Finset ι) := by simpa using fun h => h6p h.symm
  have expand : ∀ (G : LyonsRow → ℚ) (g : ℤ → ℚ), ∑ χ ∈ B, G (row χ) * g (f χ) =
      G (-2, 2, 2, 2, 2, 2) * g (f χ5) + G (0, 0, 1, 1, 1, 1) * (g (f χ9) + g (f χ10)) +
        (G (0, 1, 0, 1, 1, 1) + G (0, 1, 1, 0, 1, 1) + G (0, 1, 1, 1, 0, 1) +
          G (0, 1, 1, 1, 1, 0)) * (g (f χ3) + g (f χ4)) +
        (G (1, 0, 0, 0, 0, 1) + G (1, 0, 0, 0, 1, 0) + G (1, 0, 0, 1, 0, 0) +
          G (1, 0, 1, 0, 0, 0)) * (g (f χ1) + g (f χ2)) +
        G (1, 1, 0, 0, 0, 0) * (g (f p) + g (f χ6)) +
        G (1, 1, 1, 1, 1, 1) * (g (f χ7) + g (f χ8)) := by
    intro G g
    rw [sum_mul_row_eq hM G fun χ => g (f χ)]
    simp only [LyonsLabel.rows, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]
    rw [rh1 g, rh2 g, rh3 g, rx1 g, rx2 g, rx3 g, f5, hf9, hf3, hf1,
      show ((1, 1, 0, 0, 0, 0) : LyonsRow) = principalRow from rfl, hfibP, hf7,
      Finset.sum_pair h910, Finset.sum_pair h34, Finset.sum_pair h12, Finset.sum_insert hp6,
      Finset.sum_pair h78]
    simp only [Finset.sum_singleton]
    ring
  have hfp : ((f p : ℚ))⁻¹ = 1 := by rw [hD.principal_degree]; simp
  have r_u := hD.reciprocal_sum 0
  have r_a := hD.reciprocal_sum 1
  have r_b := hD.reciprocal_sum 2
  rw [expand (fun R => ((R.fourierSum : ℚ) ^ 2 * (R.toVec 0 : ℚ)))
    (fun n => ((n : ℚ))⁻¹)] at r_u
  rw [expand (fun R => ((R.fourierSum : ℚ) ^ 2 * (R.toVec 1 : ℚ)))
    (fun n => ((n : ℚ))⁻¹)] at r_a
  rw [expand (fun R => ((R.fourierSum : ℚ) ^ 2 * (R.toVec 2 : ℚ)))
    (fun n => ((n : ℚ))⁻¹)] at r_b
  simp only [LyonsRow.toVec, LyonsRow.fourierSum, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Fin.isValue, Int.cast_neg, Int.cast_one, Int.cast_ofNat, Int.cast_zero,
    hfp] at r_u r_a r_b
  norm_num at r_u r_a r_b
  have res : ∀ χ ∈ B, ∀ R : LyonsRow, row χ = R → ∀ r : ℤ,
      -(3 * R.fourierSum + 60 * R.1) ≡ r [ZMOD 64] → f χ ≡ r [ZMOD 64] := by
    intro χ hχ R hR r hr
    have := hD.residue hχ hR
    rw [Int.ModEq] at hr ⊢
    omega
  have c₁ : f χ1 ≡ 1 [ZMOD 64] := res χ1 m1.1 _ m1.2 1 (by decide)
  have c₂ : f χ2 ≡ 1 [ZMOD 64] := res χ2 m2.1 _ m2.2 1 (by decide)
  have c₆ : f χ6 ≡ 1 [ZMOD 64] := res χ6 m6.1 _ m6.2 1 (by decide)
  have c₃ : f χ3 ≡ 52 [ZMOD 64] := res χ3 m3.1 _ m3.2 52 (by decide)
  have c₄ : f χ4 ≡ 52 [ZMOD 64] := res χ4 m4.1 _ m4.2 52 (by decide)
  have c₉ : f χ9 ≡ 52 [ZMOD 64] := res χ9 m9.1 _ m9.2 52 (by decide)
  have c₁₀ : f χ10 ≡ 52 [ZMOD 64] := res χ10 m10.1 _ m10.2 52 (by decide)
  have c₅ : f χ5 ≡ 26 [ZMOD 64] := res χ5 h5 _ hr5 26 (by decide)
  have c₇ : f χ7 ≡ 53 [ZMOD 64] := res χ7 m7.1 _ m7.2 53 (by decide)
  have c₈ : f χ8 ≡ 53 [ZMOD 64] := res χ8 m8.1 _ m8.2 53 (by decide)
  have p₅ : 0 < f χ5 → 90 ≤ f χ5 := fun hpos => by
    have := hD.pos_bound h5 hr5 hpos
    simp only [LyonsRow.fourierSum] at this
    omega
  have n₇ : f χ7 < 0 → f χ7 ≤ -75 := fun hneg => by
    have := hD.neg_bound m7.1 m7.2 hneg
    simp only [LyonsRow.fourierSum] at this
    omega
  have n₈ : f χ8 < 0 → f χ8 ≤ -75 := fun hneg => by
    have := hD.neg_bound m8.1 m8.2 hneg
    simp only [LyonsRow.fourierSum] at this
    omega
  have big : ∀ χ ∈ B, ∀ R : LyonsRow, row χ = R → R ≠ principalRow → 12 ≤ |f χ| :=
    fun χ hχ R hR hRp => hD.degree_ge χ hχ (hD.ne_principal hR hRp)
  apply lyons_configuration_P_numerical_impossibility (f χ1) (f χ2) (f χ3) (f χ4) (f χ5)
    (f χ6) (f χ7) (f χ8) (f χ9) (f χ10)
    (big χ1 m1.1 _ m1.2 (by decide)) (big χ2 m2.1 _ m2.2 (by decide))
    (big χ3 m3.1 _ m3.2 (by decide)) (big χ4 m4.1 _ m4.2 (by decide))
    (big χ5 h5 _ hr5 (by decide)) (hD.degree_ge χ6 m6.1 h6p)
    (big χ7 m7.1 _ m7.2 (by decide)) (big χ8 m8.1 _ m8.2 (by decide))
    (big χ9 m9.1 _ m9.2 (by decide)) (big χ10 m10.1 _ m10.2 (by decide))
    c₁ c₂ c₆ c₃ c₄ c₉ c₁₀ c₅ c₇ c₈ p₅ n₇ n₈
  · simp only [div_eq_mul_inv]
    linear_combination r_u
  · simp only [div_eq_mul_inv]
    linear_combination r_a - r_b
  · have : -(4 : ℚ) / f χ1 - 4 / f χ2 + 64 / f χ3 + 64 / f χ4 + 400 / f χ5 = P := by
      simp only [div_eq_mul_inv]
      linear_combination r_a - r_u
    rw [this]
    exact hD.P_pos

end CFSG.LyonsUnitaryFour
