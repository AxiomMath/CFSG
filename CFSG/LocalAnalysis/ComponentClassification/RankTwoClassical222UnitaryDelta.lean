module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222UnitaryKappa

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix
open scoped Matrix

variable {K : Type} [Field K] {σ : K →+* K} {ℓ r : ℕ}

variable (σ) in
@[expose] def hJ (u v : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) : K := ∑ s, σ (u (swapXW s)) * v s

theorem hJ_add_left (u u' v : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) :
    hJ σ (u + u') v = hJ σ u v + hJ σ u' v := by
  simp only [hJ, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hJ_add_right (u v v' : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) :
    hJ σ u (v + v') = hJ σ u v + hJ σ u v' := by
  simp only [hJ, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hJ_smul_left (c : K) (u v : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) :
    hJ σ (c • u) v = σ c * hJ σ u v := by
  simp only [hJ, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem hJ_smul_right (c : K) (u v : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) :
    hJ σ u (c • v) = c * hJ σ u v := by
  simp only [hJ, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

theorem hJ_single (p q : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) :
    hJ σ (Pi.single p (1 : K)) (Pi.single q 1) = if swapXW q = p then 1 else 0 := by
  simp only [hJ, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  split_ifs <;> simp

theorem tv2_mul_tv2' (u u' w w' : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) :
    tv2 σ u u' * tv2 σ w w' = hJ σ u' w • tv2 σ u w' :=
  tv2_mul_tv2 u u' w w'

theorem tv2_zero_right (u : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) : tv2 σ u 0 = 0 := by
  ext p q
  simp [tv2_apply]

theorem tv2_zero_left (u : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) : tv2 σ 0 u = 0 := by
  ext p q
  simp [tv2_apply]

variable (σ) in
@[expose] def cJ (v : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) :
    Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K :=
  tv2 σ v (sqZeroStd ℓ r *ᵥ v) + tv2 σ (sqZeroStd ℓ r *ᵥ v) v

theorem tv2_conj_terms (v : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) :
    tv2 σ v v * sqZeroStd ℓ r + sqZeroStd ℓ r * tv2 σ v v +
        tv2 σ v v * sqZeroStd ℓ r * tv2 σ v v =
      cJ σ v + hJ σ (sqZeroStd ℓ r *ᵥ v) v • tv2 σ v v := by
  rw [cJ, tv2_mul_sqZeroStd, sqZeroStd_mul_tv2, tv2_mul_tv2']

theorem sqZeroStd_mul_self : sqZeroStd (K := K) ℓ r * sqZeroStd ℓ r = 0 := by
  ext p q
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [sqZeroStd_apply s q]
  rcases q with d | d
  · simp only [Sum.elim_inl, mul_ite, mul_one, mul_zero]
    split_ifs with h
    · subst h
      exact sqZeroStd_col_inr p _
    · rfl
  · simp

theorem cJ_commute (v : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) :
    cJ σ v * sqZeroStd ℓ r = sqZeroStd ℓ r * cJ σ v := by
  have hSS : ∀ u : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K,
      sqZeroStd ℓ r *ᵥ (sqZeroStd ℓ r *ᵥ u) = (0 : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) := fun u => by
    rw [Matrix.mulVec_mulVec, sqZeroStd_mul_self, Matrix.zero_mulVec]
  rw [cJ, Matrix.add_mul, Matrix.mul_add, tv2_mul_sqZeroStd, tv2_mul_sqZeroStd,
    sqZeroStd_mul_tv2, sqZeroStd_mul_tv2, hSS, tv2_zero_right, tv2_zero_left, zero_add,
    add_zero]

theorem cJ_add_of_mulVec_eq_zero (u y : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K)
    (hy : sqZeroStd ℓ r *ᵥ y = 0) :
    cJ σ (u + y) = cJ σ u + tv2 σ y (sqZeroStd ℓ r *ᵥ u) + tv2 σ (sqZeroStd ℓ r *ᵥ u) y := by
  rw [cJ, cJ, Matrix.mulVec_add, hy, add_zero, tv2_add_left, tv2_add_right]
  abel

variable (K) in
@[expose] def vecA (i j : Fin ℓ) (ζ β : K) : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K :=
  Pi.single (.inl i) 1 + ζ • Pi.single (.inl j) 1 + β • Pi.single (.inr (.inl i)) 1

theorem sqZeroStd_mulVec_vecA (i j : Fin ℓ) (ζ β : K) :
    sqZeroStd ℓ r *ᵥ vecA K (r := r) i j ζ β =
      Pi.single (.inr (.inl i)) 1 + ζ • Pi.single (.inr (.inl j)) 1 := by
  simp only [vecA, Matrix.mulVec_add, Matrix.mulVec_smul, sqZeroStd_mulVec_single_inl,
    sqZeroStd_mulVec_single_inr, smul_zero, add_zero]

theorem cJ_vecA (i j : Fin ℓ) (ζ β : K) :
    cJ σ (vecA K (r := r) i j ζ β) =
      (Matrix.single (.inl i) (.inl i) 1 + Matrix.single (.inr (.inl i)) (.inr (.inl i)) 1) +
      σ ζ • (Matrix.single (.inl i) (.inl j) 1 + Matrix.single (.inr (.inl i)) (.inr (.inl j)) 1) +
      ζ • (Matrix.single (.inl j) (.inl i) 1 + Matrix.single (.inr (.inl j)) (.inr (.inl i)) 1) +
      (ζ * σ ζ) •
        (Matrix.single (.inl j) (.inl j) 1 + Matrix.single (.inr (.inl j)) (.inr (.inl j)) 1) +
      (β + σ β) • Matrix.single (.inr (.inl i)) (.inl i) 1 +
      (β * σ ζ) • Matrix.single (.inr (.inl i)) (.inl j) 1 +
      (ζ * σ β) • Matrix.single (.inr (.inl j)) (.inl i) 1 := by
  rw [cJ, sqZeroStd_mulVec_vecA]
  simp only [vecA, tv2_add_left, tv2_add_right, tv2_smul_left, tv2_smul_right, tv2_single,
    swapXW]
  module

theorem tv2_y_vecA (i j : Fin ℓ) (k : Fin r) (ζ β t : K) :
    tv2 σ (t • Pi.single (.inr (.inr k)) 1) (sqZeroStd ℓ r *ᵥ vecA K i j ζ β) +
        tv2 σ (sqZeroStd ℓ r *ᵥ vecA K i j ζ β) (t • Pi.single (.inr (.inr k)) 1) =
      t • (Matrix.single (.inr (.inr k)) (.inl i) 1 +
        σ ζ • Matrix.single (.inr (.inr k)) (.inl j) 1) +
      σ t • (Matrix.single (.inr (.inl i)) (.inr (.inr k)) 1 +
        ζ • Matrix.single (.inr (.inl j)) (.inr (.inr k)) 1) := by
  rw [sqZeroStd_mulVec_vecA]
  simp only [tv2_add_left, tv2_add_right, tv2_smul_left, tv2_smul_right, tv2_single,
    swapXW]
  module

theorem sqZeroStd_mulVec_smul_single_inr_inr (k : Fin r) (t : K) :
    sqZeroStd ℓ r *ᵥ (t • (Pi.single (.inr (.inr k)) 1 : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K)) = 0 := by
  rw [Matrix.mulVec_smul, sqZeroStd_mulVec_single_inr, smul_zero]

theorem hJ_vecA [CharP K 2] {i j : Fin ℓ} (hij : i ≠ j) (ζ β : K) :
    hJ σ (vecA K (r := r) i j ζ β) (vecA K i j ζ β) = σ β + β := by
  simp only [vecA, hJ_add_left, hJ_add_right, hJ_smul_left, hJ_smul_right, hJ_single, swapXW]
  simp [hij, Ne.symm hij]

theorem hJ_sqZeroStd_vecA [CharP K 2] {i j : Fin ℓ} (hij : i ≠ j) (ζ β : K) :
    hJ σ (sqZeroStd ℓ r *ᵥ vecA K i j ζ β) (vecA K (r := r) i j ζ β) = 1 + σ ζ * ζ := by
  rw [sqZeroStd_mulVec_vecA]
  simp only [vecA, hJ_add_left, hJ_add_right, hJ_smul_left, hJ_smul_right, hJ_single, swapXW]
  simp [hij, Ne.symm hij]
  ring

theorem hJ_vecA_add_y [CharP K 2] {i j : Fin ℓ} (hij : i ≠ j) (k : Fin r) (ζ β t : K) :
    hJ σ (vecA K i j ζ β + t • Pi.single (.inr (.inr k)) 1)
      (vecA K i j ζ β + t • Pi.single (.inr (.inr k)) 1) = σ β + β + σ t * t := by
  simp only [vecA, hJ_add_left, hJ_add_right, hJ_smul_left, hJ_smul_right, hJ_single, swapXW]
  simp [hij, Ne.symm hij]
  ring

theorem hJ_sqZeroStd_vecA_add_y [CharP K 2] {i j : Fin ℓ} (hij : i ≠ j) (k : Fin r) (ζ β t : K) :
    hJ σ (sqZeroStd ℓ r *ᵥ (vecA K i j ζ β + t • Pi.single (.inr (.inr k)) 1))
      (vecA K i j ζ β + t • Pi.single (.inr (.inr k)) 1) = 1 + σ ζ * ζ := by
  rw [Matrix.mulVec_add, sqZeroStd_mulVec_smul_single_inr_inr, add_zero, sqZeroStd_mulVec_vecA]
  simp only [vecA, hJ_add_left, hJ_add_right, hJ_smul_left, hJ_smul_right, hJ_single, swapXW]
  simp [hij, Ne.symm hij]
  ring

variable (K) in
@[expose] def vecY (k l : Fin r) (ζ : K) : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K :=
  Pi.single (.inr (.inr k)) 1 + ζ • Pi.single (.inr (.inr l)) 1

theorem sqZeroStd_mulVec_vecY (k l : Fin r) (ζ c : K) :
    sqZeroStd ℓ r *ᵥ (c • vecY K (ℓ := ℓ) k l ζ) = 0 := by
  simp only [vecY, Matrix.mulVec_smul, Matrix.mulVec_add, sqZeroStd_mulVec_single_inr,
    smul_zero, add_zero]

variable (σ) in
@[expose] def siegelP (i : Fin ℓ) (x : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) :
    Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K :=
  tv2 σ x (Pi.single (.inl i) 1) + tv2 σ (Pi.single (.inl i) 1) x

theorem hJ_vecY_left (i : Fin ℓ) (k l : Fin r) (ζ c : K) :
    hJ σ (c • vecY K k l ζ) (Pi.single (.inl i) 1) = 0 := by
  simp [vecY, hJ_add_left, hJ_smul_left, hJ_single, swapXW]

theorem hJ_vecY_right (i : Fin ℓ) (k l : Fin r) (ζ c : K) :
    hJ σ (Pi.single (.inl i) 1) (c • vecY K k l ζ) = 0 := by
  simp [vecY, hJ_add_right, hJ_smul_right, hJ_single, swapXW]

theorem hJ_vecY_w (i : Fin ℓ) (k l : Fin r) (ζ c : K) :
    hJ σ (Pi.single (.inr (.inl i)) 1) (c • vecY K k l ζ) = 0 := by
  simp [vecY, hJ_add_right, hJ_smul_right, hJ_single, swapXW]

theorem hJ_vecY_self [CharP K 2] {k l : Fin r} (hkl : k ≠ l) {ζ : K} (hζ : σ ζ * ζ = 1)
    (c : K) : hJ σ (c • vecY K (ℓ := ℓ) k l ζ) (c • vecY K k l ζ) = 0 := by
  have h : hJ σ (vecY K (ℓ := ℓ) k l ζ) (vecY K k l ζ) = 1 + σ ζ * ζ := by
    simp only [vecY, hJ_add_left, hJ_add_right, hJ_smul_left, hJ_smul_right, hJ_single, swapXW]
    simp [hkl, Ne.symm hkl]
    ring
  rw [hJ_smul_left, hJ_smul_right, h, hζ, CharTwo.add_self_eq_zero, mul_zero, mul_zero]

theorem siegelP_mul_self [CharP K 2] (i : Fin ℓ) {k l : Fin r} (hkl : k ≠ l) {ζ : K}
    (hζ : σ ζ * ζ = 1) (c : K) : siegelP σ i (c • vecY K k l ζ) * siegelP σ i (c • vecY K k l ζ) =
      0 := by
  have he : hJ σ (Pi.single (.inl i) (1 : K)) (Pi.single (.inl i) 1 :
      Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) = 0 := by
    rw [hJ_single]
    simp [swapXW]
  rw [siegelP, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, tv2_mul_tv2', tv2_mul_tv2',
    tv2_mul_tv2', tv2_mul_tv2', hJ_vecY_left, hJ_vecY_right, he, hJ_vecY_self hkl hζ]
  simp

theorem siegelP_adj (hσ : ∀ x, σ (σ x) = x) (i : Fin ℓ) (x : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) :
    adjM σ (siegelP σ i x) * unitGram K ℓ r = unitGram K ℓ r * siegelP σ i x := by
  rw [siegelP, adjM_add, Matrix.add_mul, adjM_tv2_mul_unitGram hσ, adjM_tv2_mul_unitGram hσ,
    ← Matrix.mul_add, add_comm]

theorem siegelP_conj_terms (i : Fin ℓ) (k l : Fin r) (ζ c : K) :
    siegelP σ i (c • vecY K k l ζ) * sqZeroStd ℓ r +
        sqZeroStd ℓ r * siegelP σ i (c • vecY K k l ζ) +
        siegelP σ i (c • vecY K k l ζ) * sqZeroStd ℓ r * siegelP σ i (c • vecY K k l ζ) =
      tv2 σ (c • vecY K k l ζ) (Pi.single (.inr (.inl i)) 1) +
        tv2 σ (Pi.single (.inr (.inl i)) 1) (c • vecY K k l ζ) +
        tv2 σ (c • vecY K k l ζ) (c • vecY K k l ζ) := by
  have hw : hJ σ (Pi.single (.inr (.inl i)) (1 : K)) (Pi.single (.inl i) 1 :
      Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) = 1 := by
    rw [hJ_single]
    simp [swapXW]
  have hPS : siegelP σ i (c • vecY K k l ζ) * sqZeroStd ℓ r =
      tv2 σ (c • vecY K k l ζ) (Pi.single (.inr (.inl i)) 1) := by
    rw [siegelP, Matrix.add_mul, tv2_mul_sqZeroStd, tv2_mul_sqZeroStd,
      sqZeroStd_mulVec_single_inl, sqZeroStd_mulVec_vecY, tv2_zero_right, add_zero]
  rw [hPS, siegelP, Matrix.mul_add, sqZeroStd_mul_tv2, sqZeroStd_mul_tv2,
    sqZeroStd_mulVec_single_inl, sqZeroStd_mulVec_vecY, tv2_zero_left, zero_add, Matrix.mul_add,
    tv2_mul_tv2', tv2_mul_tv2', hJ_vecY_w, hw, zero_smul, zero_add, one_smul]

theorem siegelP_conj_commute (i : Fin ℓ) (k l : Fin r) (ζ c : K) :
    Commute (tv2 σ (c • vecY K k l ζ) (Pi.single (.inr (.inl i)) 1) +
        tv2 σ (Pi.single (.inr (.inl i)) 1) (c • vecY K k l ζ) +
        tv2 σ (c • vecY K k l ζ) (c • vecY K k l ζ)) (sqZeroStd ℓ r) := by
  rw [Commute, SemiconjBy, Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    tv2_mul_sqZeroStd, tv2_mul_sqZeroStd, tv2_mul_sqZeroStd, sqZeroStd_mul_tv2,
    sqZeroStd_mul_tv2, sqZeroStd_mul_tv2, sqZeroStd_mulVec_vecY,
    sqZeroStd_mulVec_single_inr, tv2_zero_right, tv2_zero_right, tv2_zero_left,
    tv2_zero_left]

theorem siegel_expand (i : Fin ℓ) (k l : Fin r) (ζ c : K) :
    tv2 σ (c • vecY K k l ζ) (Pi.single (.inr (.inl i)) 1) +
        tv2 σ (Pi.single (.inr (.inl i)) 1) (c • vecY K k l ζ) +
        tv2 σ (c • vecY K k l ζ) (c • vecY K k l ζ) =
      c • (Matrix.single (.inr (.inr k)) (.inl i) 1 +
        ζ • Matrix.single (.inr (.inr l)) (.inl i) 1) +
      σ c • (Matrix.single (.inr (.inl i)) (.inr (.inr k)) 1 +
        σ ζ • Matrix.single (.inr (.inl i)) (.inr (.inr l)) 1) +
      (c * σ c) • (Matrix.single (.inr (.inr k)) (.inr (.inr k)) 1 +
        σ ζ • Matrix.single (.inr (.inr k)) (.inr (.inr l)) 1 +
        ζ • Matrix.single (.inr (.inr l)) (.inr (.inr k)) 1 +
        (ζ * σ ζ) • Matrix.single (.inr (.inr l)) (.inr (.inr l)) 1) := by
  simp only [vecY, tv2_add_left, tv2_add_right, tv2_smul_left, tv2_smul_right, tv2_single,
    swapXW]
  module

section Commutant

theorem commute_of_smul_ne_zero {ι : Type} [Fintype ι] [DecidableEq ι]
    {B Z : Matrix ι ι K} {c : K} (hc : c ≠ 0) (h : Commute B (c • Z)) : Commute B Z := by
  have h1 := h.smul_right c⁻¹
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h1

theorem commute_of_eq {ι : Type} [Fintype ι] [DecidableEq ι] {B X Y : Matrix ι ι K}
    (h : Commute B X) (e : X = Y) : Commute B Y := e ▸ h

variable (σ) in
@[expose] def QuadSep : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B X Y Y' : Matrix ι ι K),
    (∀ t : K, Commute B ((σ t * t) • X + (t • Y + σ t • Y'))) → Commute B X

theorem quadSep_of_fixed {μ : K} (hμσ : σ μ = μ) (hμ0 : μ ≠ 0) (hμ1 : μ ≠ 1) : QuadSep σ := by
  intro ι _ _ B X Y Y' h
  have hμμ : μ - μ * μ ≠ 0 := by
    rw [show μ - μ * μ = μ * (1 - μ) by ring]
    exact mul_ne_zero hμ0 (sub_ne_zero.mpr (Ne.symm hμ1))
  refine commute_of_smul_ne_zero hμμ (commute_of_eq (((h 1).smul_right μ).sub_right (h μ)) ?_)
  rw [map_one, hμσ]
  module

theorem quadSep_of_cube [CharP K 2] {ω : K} (hσω : σ ω = ω * ω) (hω3 : ω * ω * ω = 1)
    (hω1 : ω ≠ 1) : QuadSep σ := by
  intro ι _ _ B X Y Y' h
  have h3 : 1 + ω + ω * ω = 0 := by
    have h0 : (ω - 1) * (1 + ω + ω * ω) = 0 := by linear_combination hω3
    exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hω1)
  have e1 : σ 1 * 1 + σ ω * ω + σ (ω * ω) * (ω * ω) = 1 := by
    rw [map_one, map_mul, hσω]
    linear_combination (ω * ω * ω + 2) * hω3 + CharTwo.two_eq_zero (R := K)
  have e3 : σ 1 + σ ω + σ (ω * ω) = 0 := by
    rw [map_one, map_mul, hσω]
    linear_combination h3 + ω * hω3
  refine commute_of_eq (((h 1).add_right (h ω)).add_right (h (ω * ω))) ?_
  calc _ = (σ 1 * 1 + σ ω * ω + σ (ω * ω) * (ω * ω)) • X +
        ((1 + ω + ω * ω) • Y + (σ 1 + σ ω + σ (ω * ω)) • Y') := by module
    _ = X := by simp only [e1, h3, e3, zero_smul, add_zero, one_smul]

variable [CharP K 2]

theorem eq_of_commute_unitary_conj (hσ : ∀ x, σ (σ x) = x) (hℓ0 : ℓ ≠ 0)
    (hcard : 4 ≤ 2 * ℓ + r)
    {B : Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K}
    (hBS : Commute B (sqZeroStd ℓ r))
    (hC : ∀ P : Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K, P * P = 0 →
      adjM σ P * unitGram K ℓ r = unitGram K ℓ r * P →
      Commute (P * sqZeroStd ℓ r + sqZeroStd ℓ r * P + P * sqZeroStd ℓ r * P) (sqZeroStd ℓ r) →
      Commute B (P * sqZeroStd ℓ r + sqZeroStd ℓ r * P + P * sqZeroStd ℓ r * P))
    {z : K} (hz : σ z * z = 1) (hz1 : z ≠ 1) (hsep : QuadSep σ) {θ : K} (hθ : σ θ ≠ θ)
    (htr : ∀ c, σ c = c → ∃ d, d + σ d = c) :
    ∃ c d : K, B = c • 1 + d • sqZeroStd ℓ r := by
  have hcv : ∀ v, hJ σ v v = 0 → hJ σ (sqZeroStd ℓ r *ᵥ v) v = 0 → Commute B (cJ σ v) := by
    intro v h1 h2
    have hP2 : tv2 σ v v * tv2 σ v v = 0 := by rw [tv2_mul_tv2', h1, zero_smul]
    have h := hC _ hP2 (adjM_tv2_mul_unitGram hσ v v) (by
      rw [tv2_conj_terms, h2, zero_smul, add_zero]
      exact cJ_commute v)
    rwa [tv2_conj_terms, h2, zero_smul, add_zero] at h
  have hsg : ∀ (i : Fin ℓ) (k l : Fin r), k ≠ l → ∀ ζ : K, σ ζ * ζ = 1 → ∀ c : K,
      Commute B (c • (Matrix.single (.inr (.inr k)) (.inl i) 1 +
        ζ • Matrix.single (.inr (.inr l)) (.inl i) 1) +
      σ c • (Matrix.single (.inr (.inl i)) (.inr (.inr k)) 1 +
        σ ζ • Matrix.single (.inr (.inl i)) (.inr (.inr l)) 1) +
      (c * σ c) • (Matrix.single (.inr (.inr k)) (.inr (.inr k)) 1 +
        σ ζ • Matrix.single (.inr (.inr k)) (.inr (.inr l)) 1 +
        ζ • Matrix.single (.inr (.inr l)) (.inr (.inr k)) 1 +
        (ζ * σ ζ) • Matrix.single (.inr (.inr l)) (.inr (.inr l)) 1)) := by
    intro i k l hkl ζ hζ c
    have h := hC (siegelP σ i (c • vecY K k l ζ)) (siegelP_mul_self i hkl hζ c)
      (siegelP_adj hσ i _) (by rw [siegelP_conj_terms]; exact siegelP_conj_commute i k l ζ c)
    rwa [siegelP_conj_terms, siegel_expand] at h
  have hσz1 : σ z ≠ 1 := fun h => hz1 (by rw [← hσ z, h, map_one])
  have hzσz : z ≠ σ z := fun h => mul_self_ne_one_of_ne_one hz1 (by
    have h2 := hz
    rw [← h] at h2
    exact h2)
  have hz2 : σ (z * z) * (z * z) = 1 := by
    rw [map_mul]
    calc σ z * σ z * (z * z) = (σ z * z) * (σ z * z) := by ring
      _ = 1 := by rw [hz, one_mul]
  have hzz : z * σ z = 1 := by rw [mul_comm]; exact hz
  have hzz2 : z * z * (σ z * σ z) = 1 := by
    calc z * z * (σ z * σ z) = (σ z * z) * (σ z * z) := by ring
      _ = 1 := by rw [hz, one_mul]
  have hone : σ 1 * (1 : K) = 1 := by rw [map_one, one_mul]
  have hθ0 : θ - σ θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ)
  have h2two : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have hS1 : ∀ i j : Fin ℓ, i ≠ j → ∀ ζ : K, σ ζ * ζ = 1 →
      Commute B (σ ζ • Matrix.single (.inr (.inl i)) (.inl j) 1 +
        ζ • Matrix.single (.inr (.inl j)) (.inl i) 1) := by
    intro i j hij ζ hζ
    have hA : ∀ β : K, σ β + β = 0 → Commute B (cJ σ (vecA K i j ζ β)) := fun β hβ =>
      hcv _ (by rw [hJ_vecA hij]; exact hβ) (by rw [hJ_sqZeroStd_vecA hij, hζ]; exact h2two)
    refine commute_of_eq ((hA 1 (by rw [map_one]; exact h2two)).sub_right (hA 0 (by simp))) ?_
    rw [cJ_vecA, cJ_vecA, map_one, map_zero, h2two]
    module
  have hC1 : ∀ i j : Fin ℓ, i ≠ j → Commute B (Matrix.single (.inr (.inl i)) (.inl j) 1) := by
    intro i j hij
    have h : Commute B ((z - σ z) • Matrix.single (.inr (.inl i)) (.inl j) 1) := by
      refine commute_of_eq (((hS1 i j hij 1 hone).smul_right z).sub_right (hS1 i j hij z hz)) ?_
      rw [map_one]
      module
    exact commute_of_smul_ne_zero (sub_ne_zero.mpr hzσz) h
  have hC4 : ∀ i j : Fin ℓ, i ≠ j →
      Commute B (Matrix.single (.inl i) (.inl j) 1 +
        Matrix.single (.inr (.inl i)) (.inr (.inl j)) 1) := by
    intro i j hij
    have hG : ∀ ζ : K, σ ζ * ζ = 1 → Commute B (cJ σ (vecA K (r := r) i j ζ 0)) := fun ζ hζ =>
      hcv _ (by rw [hJ_vecA hij]; simp) (by rw [hJ_sqZeroStd_vecA hij, hζ]; exact h2two)
    have h1 := hG 1 hone
    have h : Commute B (((1 - σ z) * (z - σ z)) • (Matrix.single (.inl i) (.inl j) 1 +
        Matrix.single (.inr (.inl i)) (.inr (.inl j)) 1)) := by
      refine commute_of_eq (((h1.sub_right (hG z hz)).smul_right (1 + z)).sub_right
        (h1.sub_right (hG (z * z) hz2))) ?_
      rw [cJ_vecA, cJ_vecA, cJ_vecA, map_one, map_zero, map_mul, hzz, hzz2]
      module
    exact commute_of_smul_ne_zero
      (mul_ne_zero (sub_ne_zero.mpr (Ne.symm hσz1)) (sub_ne_zero.mpr hzσz)) h
  have hY : ∀ i : Fin ℓ, ∀ k : Fin r, (∃ j : Fin ℓ, j ≠ i) ∨ (∃ l : Fin r, l ≠ k) →
      Commute B (Matrix.single (.inr (.inr k)) (.inl i) 1) ∧
        Commute B (Matrix.single (.inr (.inl i)) (.inr (.inr k)) 1) := by
    intro i k hjl
    rcases hjl with ⟨j, hji⟩ | ⟨l, hlk⟩
    ·
      have hij : i ≠ j := Ne.symm hji
      have hYζ : ∀ ζ : K, σ ζ * ζ = 1 →
          Commute B (Matrix.single (.inr (.inr k)) (.inl i) 1 +
            σ ζ • Matrix.single (.inr (.inr k)) (.inl j) 1) ∧
          Commute B (Matrix.single (.inr (.inl i)) (.inr (.inr k)) 1 +
            ζ • Matrix.single (.inr (.inl j)) (.inr (.inr k)) 1) := by
        intro ζ hζ
        have hW : ∀ t : K, Commute B ((σ t * t) • Matrix.single (.inr (.inl i)) (.inl i) 1 +
            (t • (Matrix.single (.inr (.inr k)) (.inl i) 1 +
              σ ζ • Matrix.single (.inr (.inr k)) (.inl j) 1) +
            σ t • (Matrix.single (.inr (.inl i)) (.inr (.inr k)) 1 +
              ζ • Matrix.single (.inr (.inl j)) (.inr (.inr k)) 1))) := by
          intro t
          obtain ⟨β, hβ⟩ := htr (σ t * t) (by rw [map_mul, hσ, mul_comm])
          have h0 := hcv (vecA K i j ζ β + t • Pi.single (.inr (.inr k)) 1)
            (by rw [hJ_vecA_add_y hij, add_comm (σ β), hβ]; exact CharTwo.add_self_eq_zero _)
            (by rw [hJ_sqZeroStd_vecA_add_y hij, hζ]; exact h2two)
          have h00 := hcv (vecA K (r := r) i j ζ 0) (by rw [hJ_vecA hij]; simp)
            (by rw [hJ_sqZeroStd_vecA hij, hζ]; exact h2two)
          refine commute_of_eq (((h0.sub_right h00).sub_right
            ((hC1 i j hij).smul_right (β * σ ζ))).sub_right
            ((hC1 j i hji).smul_right (ζ * σ β))) ?_
          rw [cJ_add_of_mulVec_eq_zero _ _ (sqZeroStd_mulVec_smul_single_inr_inr k t),
            add_assoc (cJ σ _), tv2_y_vecA, cJ_vecA, cJ_vecA, map_zero, ← hβ]
          module
        have hD : Commute B (Matrix.single (.inr (.inl i)) (.inl i) 1) := hsep _ _ _ _ _ hW
        have h12 : Commute B ((Matrix.single (.inr (.inr k)) (.inl i) 1 +
              σ ζ • Matrix.single (.inr (.inr k)) (.inl j) 1) +
            (Matrix.single (.inr (.inl i)) (.inr (.inr k)) 1 +
              ζ • Matrix.single (.inr (.inl j)) (.inr (.inr k)) 1)) := by
          refine commute_of_eq ((hW 1).sub_right hD) ?_
          rw [map_one]
          module
        have h1 : Commute B (Matrix.single (.inr (.inl i)) (.inr (.inr k)) 1 +
            ζ • Matrix.single (.inr (.inl j)) (.inr (.inr k)) 1) := by
          have h : Commute B ((θ - σ θ) • (Matrix.single (.inr (.inl i)) (.inr (.inr k)) 1 +
              ζ • Matrix.single (.inr (.inl j)) (.inr (.inr k)) 1)) := by
            refine commute_of_eq ((h12.smul_right θ).sub_right
              ((hW θ).sub_right (hD.smul_right (σ θ * θ)))) ?_
            module
          exact commute_of_smul_ne_zero hθ0 h
        refine ⟨commute_of_eq (h12.sub_right h1) ?_, h1⟩
        module
      obtain ⟨hA2, hA1⟩ := hYζ 1 hone
      obtain ⟨hB2, hB1⟩ := hYζ z hz
      constructor
      · have hj : Commute B (Matrix.single (.inr (.inr k)) (.inl j) 1) := by
          have h : Commute B ((1 - σ z) • Matrix.single (.inr (.inr k)) (.inl j) 1) := by
            refine commute_of_eq (hA2.sub_right hB2) ?_
            rw [map_one]
            module
          exact commute_of_smul_ne_zero (sub_ne_zero.mpr (Ne.symm hσz1)) h
        refine commute_of_eq (hA2.sub_right (hj.smul_right (σ 1))) ?_
        module
      · have hj : Commute B (Matrix.single (.inr (.inl j)) (.inr (.inr k)) 1) := by
          have h : Commute B ((1 - z) • Matrix.single (.inr (.inl j)) (.inr (.inr k)) 1) := by
            refine commute_of_eq (hA1.sub_right hB1) ?_
            module
          exact commute_of_smul_ne_zero (sub_ne_zero.mpr (Ne.symm hz1)) h
        refine commute_of_eq (hA1.sub_right (hj.smul_right 1)) ?_
        module
    ·
      have hkl : k ≠ l := Ne.symm hlk
      have hLζ : ∀ ζ : K, σ ζ * ζ = 1 →
          Commute B (Matrix.single (.inr (.inr k)) (.inl i) 1 +
            ζ • Matrix.single (.inr (.inr l)) (.inl i) 1) ∧
          Commute B (Matrix.single (.inr (.inl i)) (.inr (.inr k)) 1 +
            σ ζ • Matrix.single (.inr (.inl i)) (.inr (.inr l)) 1) := by
        intro ζ hζ
        have hV := hsg i k l hkl ζ hζ
        have hQ : Commute B (Matrix.single (.inr (.inr k)) (.inr (.inr k)) 1 +
            σ ζ • Matrix.single (.inr (.inr k)) (.inr (.inr l)) 1 +
            ζ • Matrix.single (.inr (.inr l)) (.inr (.inr k)) 1 +
            (ζ * σ ζ) • Matrix.single (.inr (.inr l)) (.inr (.inr l)) 1) :=
          hsep _ B _ (Matrix.single (.inr (.inr k)) (.inl i) 1 +
              ζ • Matrix.single (.inr (.inr l)) (.inl i) 1)
            (Matrix.single (.inr (.inl i)) (.inr (.inr k)) 1 +
              σ ζ • Matrix.single (.inr (.inl i)) (.inr (.inr l)) 1)
            fun c => commute_of_eq (hV c) (by module)
        have h12 : Commute B ((Matrix.single (.inr (.inr k)) (.inl i) 1 +
              ζ • Matrix.single (.inr (.inr l)) (.inl i) 1) +
            (Matrix.single (.inr (.inl i)) (.inr (.inr k)) 1 +
              σ ζ • Matrix.single (.inr (.inl i)) (.inr (.inr l)) 1)) := by
          refine commute_of_eq ((hV 1).sub_right hQ) ?_
          rw [map_one]
          module
        have h2 : Commute B (Matrix.single (.inr (.inl i)) (.inr (.inr k)) 1 +
            σ ζ • Matrix.single (.inr (.inl i)) (.inr (.inr l)) 1) := by
          have h : Commute B ((θ - σ θ) • (Matrix.single (.inr (.inl i)) (.inr (.inr k)) 1 +
              σ ζ • Matrix.single (.inr (.inl i)) (.inr (.inr l)) 1)) := by
            refine commute_of_eq ((h12.smul_right θ).sub_right
              ((hV θ).sub_right (hQ.smul_right (θ * σ θ)))) ?_
            module
          exact commute_of_smul_ne_zero hθ0 h
        exact ⟨commute_of_eq (h12.sub_right h2) (by module), h2⟩
      obtain ⟨hA1, hA2⟩ := hLζ 1 hone
      obtain ⟨hB1, hB2⟩ := hLζ z hz
      constructor
      · have hl : Commute B (Matrix.single (.inr (.inr l)) (.inl i) 1) := by
          have h : Commute B ((1 - z) • Matrix.single (.inr (.inr l)) (.inl i) 1) := by
            refine commute_of_eq (hA1.sub_right hB1) ?_
            module
          exact commute_of_smul_ne_zero (sub_ne_zero.mpr (Ne.symm hz1)) h
        refine commute_of_eq (hA1.sub_right (hl.smul_right 1)) ?_
        module
      · have hl : Commute B (Matrix.single (.inr (.inl i)) (.inr (.inr l)) 1) := by
          have h : Commute B ((1 - σ z) • Matrix.single (.inr (.inl i)) (.inr (.inr l)) 1) := by
            refine commute_of_eq (hA2.sub_right hB2) ?_
            rw [map_one]
            module
          exact commute_of_smul_ne_zero (sub_ne_zero.mpr (Ne.symm hσz1)) h
        refine commute_of_eq (hA2.sub_right (hl.smul_right (σ 1))) ?_
        module
  have hidx : ∀ (i : Fin ℓ) (k : Fin r), (∃ j : Fin ℓ, j ≠ i) ∨ (∃ l : Fin r, l ≠ k) := by
    intro i k
    rcases Nat.lt_or_ge ℓ 2 with hl1 | hl2
    · right
      have : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr (by omega)
      exact exists_ne k
    · left
      have : Nontrivial (Fin ℓ) := Fin.nontrivial_iff_two_le.mpr hl2
      exact exists_ne i
  exact commutant_kappa hℓ0 (by omega) hBS hC1 (fun k j => (hY j k (hidx j k)).1)
    (fun i k => (hY i k (hidx i k)).2) hC4

end Commutant

end CFSG.ComponentClassification.RankTwoClassical
