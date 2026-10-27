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

theorem lyons_signedDegree_ne_N (hD : LyonsSignedDegreeData B row f p N P) :
    B.val.map row ≠ lyonsConfiguration .N := by
  intro hM
  have hcount : ∀ R, (B.val.map row).count R = (lyonsConfiguration .N).count R :=
    fun R => by rw [hM]
  obtain ⟨χq, hq, hrq, huq⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (-2, 2, 2, 2, 2, 2)) (by rw [hcount]; decide)
  obtain ⟨h1, h2, hh12, hfh⟩ := rowFiber_eq_pair (B := B) (row := row) (R := (0, 1, 0, 1, 1, 1))
    (by rw [hcount]; decide)
  obtain ⟨x1, x2, hx12, hfx⟩ := rowFiber_eq_pair (B := B) (row := row) (R := (1, 0, 0, 0, 0, 1))
    (by rw [hcount]; decide)
  obtain ⟨y1, y2, hy1p, hy2p, hy12, hfibP⟩ := rowFiber_eq_triple hD.principal_mem
    hD.principal_row (by rw [hcount]; decide)
  obtain ⟨χz, hz, hrz, huz⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (1, 1, 2, 2, 2, 2)) (by rw [hcount]; decide)
  have hh1 : h1 ∈ B ∧ row h1 = (0, 1, 0, 1, 1, 1) := mem_rowFiber.mp (by rw [hfh]; simp)
  have hh2 : h2 ∈ B ∧ row h2 = (0, 1, 0, 1, 1, 1) := mem_rowFiber.mp (by rw [hfh]; simp)
  have hx1 : x1 ∈ B ∧ row x1 = (1, 0, 0, 0, 0, 1) := mem_rowFiber.mp (by rw [hfx]; simp)
  have hx2 : x2 ∈ B ∧ row x2 = (1, 0, 0, 0, 0, 1) := mem_rowFiber.mp (by rw [hfx]; simp)
  have hy1 : y1 ∈ B ∧ row y1 = principalRow := mem_rowFiber.mp (by rw [hfibP]; simp)
  have hy2 : y2 ∈ B ∧ row y2 = principalRow := mem_rowFiber.mp (by rw [hfibP]; simp)
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
  have fq := rowFiber_eq_singleton hq hrq huq
  have fz := rowFiber_eq_singleton hz hrz huz
  have hpy : p ∉ ({y1, y2} : Finset ι) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hy1p h.symm, fun h => hy2p h.symm⟩
  have expand : ∀ (G : LyonsRow → ℚ) (g : ℤ → ℚ), ∑ χ ∈ B, G (row χ) * g (f χ) =
      G (-2, 2, 2, 2, 2, 2) * g (f χq) +
        (G (0, 1, 0, 1, 1, 1) + G (0, 1, 1, 0, 1, 1) + G (0, 1, 1, 1, 0, 1) +
          G (0, 1, 1, 1, 1, 0)) * (g (f h1) + g (f h2)) +
        (G (1, 0, 0, 0, 0, 1) + G (1, 0, 0, 0, 1, 0) + G (1, 0, 0, 1, 0, 0) +
          G (1, 0, 1, 0, 0, 0)) * (g (f x1) + g (f x2)) +
        G (1, 1, 0, 0, 0, 0) * (g (f p) + (g (f y1) + g (f y2))) +
        G (1, 1, 2, 2, 2, 2) * g (f χz) := by
    intro G g
    rw [sum_mul_row_eq hM G fun χ => g (f χ)]
    simp only [LyonsLabel.rows, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]
    rw [rh1 g, rh2 g, rh3 g, rx1 g, rx2 g, rx3 g, hfh, hfx, fq, fz,
      show ((1, 1, 0, 0, 0, 0) : LyonsRow) = principalRow from rfl, hfibP,
      Finset.sum_pair hh12, Finset.sum_pair hx12, Finset.sum_insert hpy, Finset.sum_pair hy12]
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
  have c₁ : f x1 ≡ 1 [ZMOD 64] := by
    have := hD.residue hx1.1 hx1.2
    simp only [LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have c₂ : f x2 ≡ 1 [ZMOD 64] := by
    have := hD.residue hx2.1 hx2.2
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
  have e₁ : f h1 ≡ 52 [ZMOD 64] := by
    have := hD.residue hh1.1 hh1.2
    simp only [LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have e₂ : f h2 ≡ 52 [ZMOD 64] := by
    have := hD.residue hh2.1 hh2.2
    simp only [LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have cq : f χq ≡ 26 [ZMOD 64] := by
    have := hD.residue hq hrq
    simp only [LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have cz : f χz ≡ 41 [ZMOD 64] := by
    have := hD.residue hz hrz
    simp only [LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have hq90 : 0 < f χq → 90 ≤ f χq := fun hpos => by
    have := hD.pos_bound hq hrq hpos
    simp only [LyonsRow.fourierSum] at this
    omega
  have nz : f χz < 0 → f χz ≤ -87 := fun hneg => by
    have := hD.neg_bound hz hrz hneg
    simp only [LyonsRow.fourierSum] at this
    omega
  have hx₁ : 12 ≤ |f x1| := hD.degree_ge x1 hx1.1 (hD.ne_principal hx1.2 (by decide))
  have hx₂ : 12 ≤ |f x2| := hD.degree_ge x2 hx2.1 (hD.ne_principal hx2.2 (by decide))
  have hy₁ : 12 ≤ |f y1| := hD.degree_ge y1 hy1.1 hy1p
  have hy₂ : 12 ≤ |f y2| := hD.degree_ge y2 hy2.1 hy2p
  apply lyons_N_arithmetic (f x1) (f x2) (f h1) (f h2) (f χq) (f χz) (f y1) (f y2) hx₁ hx₂ hy₁
    hy₂ c₁ c₂ d₁ d₂ e₁ e₂ cq cz hq90 nz
  · intro hne q hqp hdvd
    have hh1p : h1 ≠ p := hD.ne_principal hh1.2 (by decide)
    have hh2p : h2 ≠ p := hD.ne_principal hh2.2 (by decide)
    have hfh21 : rowFiber B row (0, 1, 0, 1, 1, 1) = {h2, h1} := by
      rw [hfh, Finset.pair_comm]
    have hp1 := hD.prime_le_of_unique hh1.1 hh1p (unique_degree_of_pair hfh hne)
    have hp2 := hD.prime_le_of_unique hh2.1 hh2p (unique_degree_of_pair hfh21 (Ne.symm hne))
    rcases hdvd with hdvd | hdvd | hdvd
    · exact ⟨hp1 h1 hh1.1 q hqp hdvd, hp2 h1 hh1.1 q hqp hdvd⟩
    · exact ⟨hp1 h2 hh2.1 q hqp hdvd, hp2 h2 hh2.1 q hqp hdvd⟩
    · exact ⟨hp1 χq hq q hqp hdvd, hp2 χq hq q hqp hdvd⟩
  · simp only [div_eq_mul_inv]
    linear_combination r_u
  · simp only [div_eq_mul_inv]
    linear_combination r_u + r_a - r_b

end CFSG.LyonsUnitaryFour
