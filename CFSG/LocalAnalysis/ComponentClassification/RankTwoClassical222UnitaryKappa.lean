module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222UnitaryNF
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222LinearPair

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix
open scoped Matrix

variable {K : Type} [Field K] {ℓ r : ℕ}

theorem eq_swapXW_iff {p q : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)} : q = swapXW p ↔ p = swapXW q := by
  constructor
  · rintro rfl
    rw [swapXW_swapXW]
  · rintro rfl
    rw [swapXW_swapXW]

theorem mul_unitGram_apply (Z : Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K)
    (p q : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) : (Z * unitGram K ℓ r) p q = Z p (swapXW q) := by
  simp only [Matrix.mul_apply, unitGram, Matrix.of_apply, mul_ite, mul_one, mul_zero,
    eq_swapXW_iff, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem unitGram_mul_apply (Z : Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K)
    (p q : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) : (unitGram K ℓ r * Z) p q = Z (swapXW p) q := by
  simp only [Matrix.mul_apply, unitGram, Matrix.of_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

variable (σ : K →+* K) in
@[expose] def tv2 (u u' : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) :
    Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K :=
  Matrix.of fun p q => u p * σ (u' (swapXW q))

variable {σ : K →+* K}

theorem tv2_apply (u u' : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) (p q : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) :
    tv2 σ u u' p q = u p * σ (u' (swapXW q)) := rfl

theorem tv2_add_left (u₁ u₂ u' : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) :
    tv2 σ (u₁ + u₂) u' = tv2 σ u₁ u' + tv2 σ u₂ u' := by
  ext p q
  simp only [tv2_apply, Pi.add_apply, Matrix.add_apply, add_mul]

theorem tv2_add_right (u u'₁ u'₂ : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) :
    tv2 σ u (u'₁ + u'₂) = tv2 σ u u'₁ + tv2 σ u u'₂ := by
  ext p q
  simp only [tv2_apply, Pi.add_apply, Matrix.add_apply, map_add, mul_add]

theorem tv2_smul_left (c : K) (u u' : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) :
    tv2 σ (c • u) u' = c • tv2 σ u u' := by
  ext p q
  simp only [tv2_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, mul_assoc]

theorem tv2_smul_right (c : K) (u u' : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) :
    tv2 σ u (c • u') = σ c • tv2 σ u u' := by
  ext p q
  simp only [tv2_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, map_mul]
  ring

theorem tv2_single (p q : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) :
    tv2 σ (Pi.single p (1 : K)) (Pi.single q 1) = Matrix.single p (swapXW q) 1 := by
  ext p' q'
  simp only [tv2_apply, Pi.single_apply, Matrix.single_apply]
  by_cases h1 : p' = p
  · by_cases h2 : swapXW q' = q
    · have h3 : swapXW q = q' := by rw [← h2, swapXW_swapXW]
      simp [h1, h2, h3]
    · have h3 : swapXW q ≠ q' := fun h => h2 (by rw [← h, swapXW_swapXW])
      simp [h1, h2, h3]
  · have h3 : p ≠ p' := Ne.symm h1
    simp [h1, h3]

theorem tv2_mul_tv2 (u u' w w' : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) :
    tv2 σ u u' * tv2 σ w w' = (∑ s, σ (u' (swapXW s)) * w s) • tv2 σ u w' := by
  ext p q
  simp only [Matrix.mul_apply, tv2_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

theorem adjM_tv2_mul_unitGram (hσ : ∀ x, σ (σ x) = x) (u u' : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) :
    adjM σ (tv2 σ u u') * unitGram K ℓ r = unitGram K ℓ r * tv2 σ u' u := by
  ext p q
  rw [mul_unitGram_apply, unitGram_mul_apply]
  simp only [adjM, Matrix.transpose_apply, Matrix.map_apply, tv2_apply, map_mul, hσ]
  ring

theorem adjM_one_add_mul_unitGram [CharP K 2]
    {P : Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K}
    (hP : adjM σ P * unitGram K ℓ r = unitGram K ℓ r * P) (hP2 : P * P = 0) :
    adjM σ (1 + P) * unitGram K ℓ r * (1 + P) = unitGram K ℓ r := by
  have h1 : adjM σ (1 + P) * unitGram K ℓ r = unitGram K ℓ r + unitGram K ℓ r * P := by
    rw [adjM_add, adjM_one, Matrix.add_mul, Matrix.one_mul, hP]
  rw [h1, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_one, Matrix.mul_one,
    Matrix.mul_assoc, hP2, Matrix.mul_zero, add_zero, add_assoc, matrix_add_self, add_zero]

@[simp] theorem single_mul_sqZeroStd_inr_inl (p : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (d : Fin ℓ) :
    Matrix.single p (.inr (.inl d)) (1 : K) * sqZeroStd ℓ r = Matrix.single p (.inl d) 1 := by
  ext a b
  by_cases ha : a = p
  · subst ha
    rw [single_mul_apply_same, one_mul, sqZeroStd_apply]
    rcases b with c | c
    · simp [Matrix.single_apply]
    · simp
  · rw [single_mul_apply_of_ne _ _ _ _ _ ha]
    simp [Ne.symm ha]

@[simp] theorem single_mul_sqZeroStd_inl (p : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (d : Fin ℓ) :
    Matrix.single p (.inl d) (1 : K) * sqZeroStd ℓ r = 0 :=
  single_mul_sqZeroStd_eq_zero (sqZeroStd_inl d)

@[simp] theorem single_mul_sqZeroStd_inr_inr (p : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (k : Fin r) :
    Matrix.single p (.inr (.inr k)) (1 : K) * sqZeroStd ℓ r = 0 :=
  single_mul_sqZeroStd_eq_zero (sqZeroStd_inr_inr k)

@[simp] theorem sqZeroStd_mul_single_inl (c : Fin ℓ) (q : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) :
    sqZeroStd ℓ r * Matrix.single (.inl c) q (1 : K) = Matrix.single (.inr (.inl c)) q 1 := by
  ext a b
  by_cases hb : b = q
  · subst hb
    rw [mul_single_apply_same, mul_one, sqZeroStd_apply]
    simp [Matrix.single_apply, eq_comm]
  · rw [mul_single_apply_of_ne _ _ _ _ _ hb]
    simp [Ne.symm hb]

@[simp] theorem sqZeroStd_mul_single_inr (c : Fin ℓ ⊕ Fin r) (q : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) :
    sqZeroStd ℓ r * Matrix.single (.inr c) q (1 : K) = 0 :=
  sqZeroStd_mul_single_eq_zero fun m => sqZeroStd_col_inr m c

theorem tv2_mul_sqZeroStd (u u' : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) :
    tv2 σ u u' * sqZeroStd ℓ r = tv2 σ u (sqZeroStd ℓ r *ᵥ u') := by
  ext p q
  simp only [Matrix.mul_apply, tv2_apply, Matrix.mulVec, dotProduct, sqZeroStd_apply]
  rcases q with d | d
  · simp only [Sum.elim_inl, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
    simp [swapXW]
  · simp only [Sum.elim_inr, mul_zero, Finset.sum_const_zero]
    rcases d with d | d
    · simp [swapXW]
    · simp [swapXW]

theorem sqZeroStd_mul_tv2 (u u' : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) :
    sqZeroStd ℓ r * tv2 σ u u' = tv2 σ (sqZeroStd ℓ r *ᵥ u) u' := by
  ext p q
  simp only [Matrix.mul_apply, tv2_apply, Matrix.mulVec, dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

@[simp] theorem sqZeroStd_mulVec_single_inl (c : Fin ℓ) :
    sqZeroStd (K := K) ℓ r *ᵥ Pi.single (.inl c) 1 = Pi.single (.inr (.inl c)) 1 := by
  ext m
  rw [Matrix.mulVec_single_one, Matrix.col_apply, sqZeroStd_apply, Sum.elim_inl,
    Pi.single_apply]

@[simp] theorem sqZeroStd_mulVec_single_inr (c : Fin ℓ ⊕ Fin r) :
    sqZeroStd (K := K) ℓ r *ᵥ Pi.single (.inr c) 1 = 0 := by
  ext m
  rw [Matrix.mulVec_single_one, Matrix.col_apply, sqZeroStd_apply, Sum.elim_inr,
    Pi.zero_apply]

theorem one_add_mul_one_add_mul_one_add [CharP K 2]
    {S P : Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K} (hP2 : P * P = 0) :
    (1 + P) * (1 + S) * (1 + P) = (1 + S) + (P * S + S * P + P * S * P) := by
  have h : (1 + P) * (1 + S) * (1 + P) =
      (1 + S) + (P * S + S * P + P * S * P) + (P + P) + P * P := by noncomm_ring
  rw [h, matrix_add_self, hP2, add_zero, add_zero]

end CFSG.ComponentClassification.RankTwoClassical
