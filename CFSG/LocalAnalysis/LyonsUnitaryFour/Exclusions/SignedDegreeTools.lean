module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Exclusions.RowSums
public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.SignedDegreeData
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star

public section

open scoped BigOperators

namespace CFSG.LyonsUnitaryFour

variable {ι : Type*} {B : Finset ι} {row : ι → LyonsRow} {f : ι → ℤ} {p : ι} {N : ℕ} {P : ℚ}

namespace LyonsSignedDegreeData

theorem degree_sum_rat (hD : LyonsSignedDegreeData B row f p N P) (k : Fin 6) :
    ∑ χ ∈ B, (((row χ).toVec k : ℤ) : ℚ) * (f χ : ℚ) = 0 := by
  have hcast := congrArg (fun n : ℤ => (n : ℚ)) (hD.degree_eq k)
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_zero] at hcast
  rw [← hcast]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem reciprocal_sum (hD : LyonsSignedDegreeData B row f p N P) (k : Fin 6) :
    ∑ χ ∈ B, (((row χ).fourierSum : ℚ) ^ 2 * (row χ).toVec k) * ((f χ : ℚ))⁻¹ =
      if k = 0 then 0 else P := by
  by_cases hk : k = 0
  · subst hk
    rw [ite_eq_left rfl, ← hD.reciprocal_u]
    exact Finset.sum_congr rfl fun χ _ => by rw [div_eq_mul_inv]; rfl
  · rw [ite_eq_right hk, ← hD.reciprocal_v k hk]
    exact Finset.sum_congr rfl fun χ _ => by rw [div_eq_mul_inv]

theorem residue (hD : LyonsSignedDegreeData B row f p N P) {χ : ι} (hχ : χ ∈ B)
    {R : LyonsRow} (hR : row χ = R) : (64 : ℤ) ∣ f χ + 3 * R.fourierSum + 60 * R.1 := by
  have := hD.mult_a_dvd χ hχ
  rwa [hR] at this

theorem pos_bound (hD : LyonsSignedDegreeData B row f p N P) {χ : ι} (hχ : χ ∈ B)
    {R : LyonsRow} (hR : row χ = R) (hpos : 0 < f χ) :
    0 ≤ f χ + 3 * R.fourierSum + 60 * R.1 := by
  have h := hD.mult_a_nonneg χ hχ
  rw [hR, Int.sign_eq_one_of_pos hpos, one_mul] at h
  exact h

theorem neg_bound (hD : LyonsSignedDegreeData B row f p N P) {χ : ι} (hχ : χ ∈ B)
    {R : LyonsRow} (hR : row χ = R) (hneg : f χ < 0) :
    f χ + 3 * R.fourierSum + 60 * R.1 ≤ 0 := by
  have h := hD.mult_a_nonneg χ hχ
  rw [hR, Int.sign_eq_neg_one_of_neg hneg] at h
  linarith

theorem ne_principal (hD : LyonsSignedDegreeData B row f p N P) {χ : ι} {R : LyonsRow}
    (hR : row χ = R) (hRp : R ≠ principalRow) : χ ≠ p := by
  rintro rfl
  exact hRp (hR.symm.trans hD.principal_row)

theorem prime_le_of_unique (hD : LyonsSignedDegreeData B row f p N P) {χ : ι} (hχ : χ ∈ B)
    (hχp : χ ≠ p) (huniq : ∀ ψ ∈ B, row ψ = row χ → f ψ = f χ → ψ = χ) :
    ∀ ψ ∈ B, ∀ q : ℕ, q.Prime → q ∣ (f ψ).natAbs → (q : ℤ) ≤ |f χ| + 1 :=
  fun ψ hψ q hq hdvd => hD.prime_bound χ hχ hχp huniq q hq (hdvd.trans (hD.degree_dvd ψ hψ))

end LyonsSignedDegreeData

theorem unique_degree_of_unique_row {χ : ι} {R : LyonsRow} (hR : row χ = R)
    (huniq : ∀ ψ ∈ B, row ψ = R → ψ = χ) : ∀ ψ ∈ B, row ψ = row χ → f ψ = f χ → ψ = χ :=
  fun ψ hψ hrow _ => huniq ψ hψ (hrow.trans hR)

theorem unique_degree_of_pair [DecidableEq ι] {χ₁ χ₂ : ι} {R : LyonsRow}
    (hfib : rowFiber B row R = {χ₁, χ₂}) (hne : f χ₁ ≠ f χ₂) :
    ∀ ψ ∈ B, row ψ = row χ₁ → f ψ = f χ₁ → ψ = χ₁ := by
  intro ψ hψ hrow hf
  have hχ₁ : χ₁ ∈ rowFiber B row R := by rw [hfib]; simp
  have hψR : ψ ∈ rowFiber B row R :=
    mem_rowFiber.mpr ⟨hψ, hrow.trans (mem_rowFiber.mp hχ₁).2⟩
  rw [hfib, Finset.mem_insert, Finset.mem_singleton] at hψR
  rcases hψR with h | h
  · exact h
  · exact absurd (h ▸ hf.symm) hne

end CFSG.LyonsUnitaryFour
