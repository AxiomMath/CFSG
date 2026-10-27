module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Exclusions.RowSums
public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.SignedDegreeData
public import Mathlib.Tactic.ENatToNat

public section

open scoped BigOperators

namespace CFSG.LyonsUnitaryFour

variable {ι : Type*} {B : Finset ι} {row : ι → LyonsRow} {f : ι → ℤ} {p : ι} {N : ℕ} {P : ℚ}

@[expose] def fiberDegree (B : Finset ι) (row : ι → LyonsRow) (f : ι → ℤ) (R : LyonsRow) : ℚ :=
  ∑ χ ∈ rowFiber B row R, (f χ : ℚ)

@[expose] def fiberReciprocal (B : Finset ι) (row : ι → LyonsRow) (f : ι → ℤ) (R : LyonsRow) :
    ℚ :=
  ∑ χ ∈ rowFiber B row R, ((f χ : ℚ))⁻¹

theorem exists_fiber_single {R : LyonsRow} (h : (B.val.map row).count R = 1) :
    ∃ χ ∈ B, row χ = R ∧ fiberDegree B row f R = f χ ∧
      fiberReciprocal B row f R = ((f χ : ℚ))⁻¹ := by
  obtain ⟨χ, hχ, hR, hu⟩ := exists_unique_of_count_eq_one h
  have hfib := rowFiber_eq_singleton hχ hR hu
  exact ⟨χ, hχ, hR, by rw [fiberDegree, hfib, Finset.sum_singleton],
    by rw [fiberReciprocal, hfib, Finset.sum_singleton]⟩

theorem exists_fiber_pair {R : LyonsRow} (h : (B.val.map row).count R = 2) :
    ∃ χ₁ ∈ B, ∃ χ₂ ∈ B, row χ₁ = R ∧ row χ₂ = R ∧
      fiberDegree B row f R = f χ₁ + f χ₂ ∧
      fiberReciprocal B row f R = ((f χ₁ : ℚ))⁻¹ + ((f χ₂ : ℚ))⁻¹ := by
  classical
  obtain ⟨χ₁, χ₂, hne, hfib⟩ := rowFiber_eq_pair h
  have h₁ : χ₁ ∈ B ∧ row χ₁ = R := mem_rowFiber.mp (by rw [hfib]; simp)
  have h₂ : χ₂ ∈ B ∧ row χ₂ = R := mem_rowFiber.mp (by rw [hfib]; simp)
  have hn : χ₁ ∉ ({χ₂} : Finset ι) := by simpa using hne
  exact ⟨χ₁, h₁.1, χ₂, h₂.1, h₁.2, h₂.2,
    by rw [fiberDegree, hfib, Finset.sum_insert hn, Finset.sum_singleton],
    by rw [fiberReciprocal, hfib, Finset.sum_insert hn, Finset.sum_singleton]⟩

theorem exists_fiber_triple {R : LyonsRow} (h : (B.val.map row).count R = 3) :
    ∃ χ₁ ∈ B, ∃ χ₂ ∈ B, ∃ χ₃ ∈ B, row χ₁ = R ∧ row χ₂ = R ∧ row χ₃ = R ∧
      fiberDegree B row f R = f χ₁ + f χ₂ + f χ₃ ∧
      fiberReciprocal B row f R = ((f χ₁ : ℚ))⁻¹ + ((f χ₂ : ℚ))⁻¹ + ((f χ₃ : ℚ))⁻¹ := by
  classical
  rw [← card_rowFiber] at h
  obtain ⟨χ₁, χ₂, χ₃, h₁₂, h₁₃, h₂₃, hfib⟩ := Finset.card_eq_three.mp h
  have h₁ : χ₁ ∈ B ∧ row χ₁ = R := mem_rowFiber.mp (by rw [hfib]; simp)
  have h₂ : χ₂ ∈ B ∧ row χ₂ = R := mem_rowFiber.mp (by rw [hfib]; simp)
  have h₃ : χ₃ ∈ B ∧ row χ₃ = R := mem_rowFiber.mp (by rw [hfib]; simp)
  have hn₁ : χ₁ ∉ ({χ₂, χ₃} : Finset ι) := by simp [h₁₂, h₁₃]
  have hn₂ : χ₂ ∉ ({χ₃} : Finset ι) := by simpa using h₂₃
  refine ⟨χ₁, h₁.1, χ₂, h₂.1, χ₃, h₃.1, h₁.2, h₂.2, h₃.2, ?_, ?_⟩
  · rw [fiberDegree, hfib, Finset.sum_insert hn₁, Finset.sum_insert hn₂, Finset.sum_singleton,
      add_assoc]
  · rw [fiberReciprocal, hfib, Finset.sum_insert hn₁, Finset.sum_insert hn₂,
      Finset.sum_singleton, add_assoc]

namespace LyonsSignedDegreeData

theorem degree_eq_rows (hD : LyonsSignedDegreeData B row f p N P) {c : LyonsLabel}
    (hM : B.val.map row = lyonsConfiguration c) (k : Fin 6) :
    ((c.rows.map Prod.fst).map fun R => ((R.toVec k : ℤ) : ℚ) * fiberDegree B row f R).sum =
      0 := by
  refine (sum_mul_row_eq hM (fun R => ((R.toVec k : ℤ) : ℚ)) (fun χ => (f χ : ℚ))).symm.trans ?_
  have hcast := congrArg (fun n : ℤ => (n : ℚ)) (hD.degree_eq k)
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_zero] at hcast
  rw [← hcast]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem reciprocal_rows_zero (hD : LyonsSignedDegreeData B row f p N P) {c : LyonsLabel}
    (hM : B.val.map row = lyonsConfiguration c) :
    ((c.rows.map Prod.fst).map fun R =>
      ((R.fourierSum : ℚ) ^ 2 * ((R.toVec 0 : ℤ) : ℚ)) * fiberReciprocal B row f R).sum = 0 := by
  refine (sum_mul_row_eq hM (fun R => (R.fourierSum : ℚ) ^ 2 * ((R.toVec 0 : ℤ) : ℚ))
    (fun χ => ((f χ : ℚ))⁻¹)).symm.trans ?_
  rw [← hD.reciprocal_u]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [div_eq_mul_inv]
  rfl

theorem reciprocal_rows (hD : LyonsSignedDegreeData B row f p N P) {c : LyonsLabel}
    (hM : B.val.map row = lyonsConfiguration c) (k : Fin 6) (hk : k ≠ 0) :
    ((c.rows.map Prod.fst).map fun R =>
      ((R.fourierSum : ℚ) ^ 2 * ((R.toVec k : ℤ) : ℚ)) * fiberReciprocal B row f R).sum = P := by
  refine (sum_mul_row_eq hM (fun R => (R.fourierSum : ℚ) ^ 2 * ((R.toVec k : ℤ) : ℚ))
    (fun χ => ((f χ : ℚ))⁻¹)).symm.trans ?_
  rw [← hD.reciprocal_v k hk]
  exact Finset.sum_congr rfl fun χ _ => by rw [div_eq_mul_inv]

theorem fiberDegree_rotate (hD : LyonsSignedDegreeData B row f p N P) (R : LyonsRow) :
    fiberDegree B row f R.rotate = fiberDegree B row f R := by
  obtain ⟨τ, hτ, hτrow⟩ := hD.galois
  exact sum_rowFiber_rotate τ hτ hτrow R fun n : ℤ => (n : ℚ)

theorem fiberReciprocal_rotate (hD : LyonsSignedDegreeData B row f p N P) (R : LyonsRow) :
    fiberReciprocal B row f R.rotate = fiberReciprocal B row f R := by
  obtain ⟨τ, hτ, hτrow⟩ := hD.galois
  exact sum_rowFiber_rotate τ hτ hτrow R fun n : ℤ => ((n : ℚ))⁻¹

theorem fiber_rotate (hD : LyonsSignedDegreeData B row f p N P) (R : LyonsRow) :
    fiberDegree B row f R.rotate = fiberDegree B row f R ∧
      fiberReciprocal B row f R.rotate = fiberReciprocal B row f R :=
  ⟨hD.fiberDegree_rotate R, hD.fiberReciprocal_rotate R⟩

theorem fiber_rotate_cycle (hD : LyonsSignedDegreeData B row f p N P) (R : LyonsRow) :
    fiberDegree B row f R.rotate = fiberDegree B row f R ∧
      fiberDegree B row f R.rotate.rotate = fiberDegree B row f R ∧
      fiberDegree B row f R.rotate.rotate.rotate = fiberDegree B row f R ∧
      fiberReciprocal B row f R.rotate = fiberReciprocal B row f R ∧
      fiberReciprocal B row f R.rotate.rotate = fiberReciprocal B row f R ∧
      fiberReciprocal B row f R.rotate.rotate.rotate = fiberReciprocal B row f R := by
  refine ⟨hD.fiberDegree_rotate R, ?_, ?_, hD.fiberReciprocal_rotate R, ?_, ?_⟩
  · rw [hD.fiberDegree_rotate, hD.fiberDegree_rotate]
  · rw [hD.fiberDegree_rotate, hD.fiberDegree_rotate, hD.fiberDegree_rotate]
  · rw [hD.fiberReciprocal_rotate, hD.fiberReciprocal_rotate]
  · rw [hD.fiberReciprocal_rotate, hD.fiberReciprocal_rotate, hD.fiberReciprocal_rotate]

theorem fiber_principal_single (hD : LyonsSignedDegreeData B row f p N P)
    (h : (B.val.map row).count principalRow = 1) :
    fiberDegree B row f principalRow = 1 ∧ fiberReciprocal B row f principalRow = 1 := by
  obtain ⟨χ, hχ, hR, hu⟩ := exists_unique_of_count_eq_one h
  have hfib := rowFiber_eq_singleton hχ hR hu
  rw [← hu p hD.principal_mem hD.principal_row] at hfib
  simp [fiberDegree, fiberReciprocal, hfib, hD.principal_degree]

theorem exists_fiber_principal_pair (hD : LyonsSignedDegreeData B row f p N P)
    (h : (B.val.map row).count principalRow = 2) :
    ∃ y ∈ B, row y = principalRow ∧ y ≠ p ∧
      fiberDegree B row f principalRow = 1 + f y ∧
      fiberReciprocal B row f principalRow = 1 + ((f y : ℚ))⁻¹ := by
  classical
  obtain ⟨y, hyp, hfib⟩ := rowFiber_eq_pair_principal hD.principal_mem hD.principal_row h
  have hy : y ∈ B ∧ row y = principalRow := mem_rowFiber.mp (by rw [hfib]; simp)
  have hn : p ∉ ({y} : Finset ι) := by simpa using Ne.symm hyp
  refine ⟨y, hy.1, hy.2, hyp, ?_, ?_⟩
  · rw [fiberDegree, hfib, Finset.sum_insert hn, Finset.sum_singleton, hD.principal_degree,
      Int.cast_one]
  · rw [fiberReciprocal, hfib, Finset.sum_insert hn, Finset.sum_singleton, hD.principal_degree,
      Int.cast_one, inv_one]

theorem exists_fiber_principal_triple (hD : LyonsSignedDegreeData B row f p N P)
    (h : (B.val.map row).count principalRow = 3) :
    ∃ y₁ ∈ B, ∃ y₂ ∈ B, row y₁ = principalRow ∧ row y₂ = principalRow ∧ y₁ ≠ p ∧ y₂ ≠ p ∧
      fiberDegree B row f principalRow = 1 + f y₁ + f y₂ ∧
      fiberReciprocal B row f principalRow = 1 + ((f y₁ : ℚ))⁻¹ + ((f y₂ : ℚ))⁻¹ := by
  classical
  obtain ⟨y₁, y₂, hy₁p, hy₂p, hy₁₂, hfib⟩ :=
    rowFiber_eq_triple hD.principal_mem hD.principal_row h
  have hy₁ : y₁ ∈ B ∧ row y₁ = principalRow := mem_rowFiber.mp (by rw [hfib]; simp)
  have hy₂ : y₂ ∈ B ∧ row y₂ = principalRow := mem_rowFiber.mp (by rw [hfib]; simp)
  have hn : p ∉ ({y₁, y₂} : Finset ι) := by simp [Ne.symm hy₁p, Ne.symm hy₂p]
  have hn' : y₁ ∉ ({y₂} : Finset ι) := by simpa using hy₁₂
  refine ⟨y₁, hy₁.1, y₂, hy₂.1, hy₁.2, hy₂.2, hy₁p, hy₂p, ?_, ?_⟩
  · rw [fiberDegree, hfib, Finset.sum_insert hn, Finset.sum_insert hn', Finset.sum_singleton,
      hD.principal_degree, Int.cast_one, add_assoc]
  · rw [fiberReciprocal, hfib, Finset.sum_insert hn, Finset.sum_insert hn',
      Finset.sum_singleton, hD.principal_degree, Int.cast_one, inv_one, add_assoc]

theorem modEq_of_row (hD : LyonsSignedDegreeData B row f p N P) {χ : ι} (hχ : χ ∈ B)
    {R : LyonsRow} (hR : row χ = R) {r : ℤ} (hr : (64 : ℤ) ∣ r + 3 * R.fourierSum + 60 * R.1) :
    f χ ≡ r [ZMOD 64] := by
  have h := hD.mult_a_dvd χ hχ
  rw [hR] at h
  rw [Int.modEq_iff_dvd]
  have := dvd_sub hr h
  rwa [show r + 3 * R.fourierSum + 60 * R.1 - (f χ + 3 * R.fourierSum + 60 * R.1) = r - f χ by
    ring] at this

theorem le_of_pos_of_row (hD : LyonsSignedDegreeData B row f p N P) {χ : ι} (hχ : χ ∈ B)
    {R : LyonsRow} (hR : row χ = R) {r : ℤ} (hr : r + 3 * R.fourierSum + 60 * R.1 = 0) :
    0 < f χ → r ≤ f χ := by
  intro hpos
  have h := hD.mult_a_nonneg χ hχ
  rw [hR, Int.sign_eq_one_of_pos hpos, one_mul] at h
  omega

theorem le_of_neg_of_row (hD : LyonsSignedDegreeData B row f p N P) {χ : ι} (hχ : χ ∈ B)
    {R : LyonsRow} (hR : row χ = R) {r : ℤ} (hr : r + 3 * R.fourierSum + 60 * R.1 = 0) :
    f χ < 0 → f χ ≤ r := by
  intro hneg
  have h := hD.mult_a_nonneg χ hχ
  rw [hR, Int.sign_eq_neg_one_of_neg hneg] at h
  omega

theorem abs_degree_ge_of_row (hD : LyonsSignedDegreeData B row f p N P) {χ : ι} (hχ : χ ∈ B)
    {R : LyonsRow} (hR : row χ = R) (hRp : R ≠ principalRow) : 12 ≤ |f χ| :=
  hD.degree_ge χ hχ fun h => hRp (hR.symm.trans ((congrArg row h).trans hD.principal_row))

end LyonsSignedDegreeData

end CFSG.LyonsUnitaryFour
