module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Enumeration.Rows
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Nat.Prime.Defs

public section

open scoped BigOperators

namespace CFSG.LyonsUnitaryFour

structure LyonsSignedDegreeData {ι : Type*} (B : Finset ι) (row : ι → LyonsRow) (f : ι → ℤ)
    (p : ι) (N : ℕ) (P : ℚ) : Prop where
  principal_mem : p ∈ B
  principal_row : row p = principalRow
  principal_degree : f p = 1
  fourierSum_pos : ∀ χ ∈ B, 0 < (row χ).fourierSum
  degree_ne_zero : ∀ χ ∈ B, f χ ≠ 0
  degree_ge : ∀ χ ∈ B, χ ≠ p → 12 ≤ |f χ|
  N_pos : 0 < N
  degree_dvd : ∀ χ ∈ B, (f χ).natAbs ∣ N
  mult_c_dvd : ∀ χ ∈ B, (16 : ℤ) ∣ f χ - (row χ).fourierSum
  mult_c_nonneg : ∀ χ ∈ B, 0 ≤ Int.sign (f χ) * (f χ - (row χ).fourierSum)
  mult_c_pos : ∀ χ ∈ B, χ ≠ p → 16 ≤ Int.sign (f χ) * (f χ - (row χ).fourierSum)
  mult_b_dvd : ∀ χ ∈ B, (64 : ℤ) ∣ f χ + 3 * (row χ).fourierSum - 4 * (row χ).1
  mult_b_nonneg : ∀ χ ∈ B,
    0 ≤ Int.sign (f χ) * (f χ + 3 * (row χ).fourierSum - 4 * (row χ).1)
  mult_a_dvd : ∀ χ ∈ B, (64 : ℤ) ∣ f χ + 3 * (row χ).fourierSum + 60 * (row χ).1
  mult_a_nonneg : ∀ χ ∈ B,
    0 ≤ Int.sign (f χ) * (f χ + 3 * (row χ).fourierSum + 60 * (row χ).1)
  degree_eq : ∀ k : Fin 6, ∑ χ ∈ B, f χ * (row χ).toVec k = 0
  reciprocal_u : ∑ χ ∈ B, ((row χ).fourierSum : ℚ) ^ 2 * (row χ).1 / f χ = 0
  reciprocal_v : ∀ k : Fin 6, k ≠ 0 →
    ∑ χ ∈ B, ((row χ).fourierSum : ℚ) ^ 2 * (row χ).toVec k / f χ = P
  P_pos : 0 < P
  galois : ∃ τ : ι → ι, Set.BijOn τ B B ∧
    ∀ χ ∈ B, row (τ χ) = (row χ).rotate ∧ f (τ χ) = f χ
  prime_bound : ∀ χ ∈ B, χ ≠ p → (∀ ψ ∈ B, row ψ = row χ → f ψ = f χ → ψ = χ) →
    ∀ q : ℕ, q.Prime → q ∣ N → (q : ℤ) ≤ |f χ| + 1

end CFSG.LyonsUnitaryFour
