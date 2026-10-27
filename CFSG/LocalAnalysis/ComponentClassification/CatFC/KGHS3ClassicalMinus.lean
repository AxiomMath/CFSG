module

public import CFSG.Open.StatedDefs

public section

namespace CFSG.ComponentClassification.CatFC.KGHS3

open Matrix CFSG.Open CFSG.MatrixModel

@[expose] def minusGram (m : ℕ) (K : Type) [Field K] (b c : K) :
    Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K :=
  Matrix.of fun r s =>
    match r, s with
    | Sum.inl i, Sum.inr (Sum.inl j) => if i = j then 1 else 0
    | Sum.inr (Sum.inl i), Sum.inl j => if i = j then 1 else 0
    | Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0) => 2
    | Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1) => b
    | Sum.inr (Sum.inr 1), Sum.inr (Sum.inr 0) => b
    | Sum.inr (Sum.inr 1), Sum.inr (Sum.inr 1) => 2 * c
    | _, _ => 0

theorem minusGram_mulVec_inl (m : ℕ) (K : Type) [Field K] (b c : K)
    (w : Fin m ⊕ Fin m ⊕ Fin 2 → K) (i : Fin m) :
    (minusGram m K b c *ᵥ w) (Sum.inl i) = w (Sum.inr (Sum.inl i)) := by
  simp [Matrix.mulVec, dotProduct, minusGram, Fintype.sum_sum_type, Fin.sum_univ_two]

theorem minusGram_mulVec_inr_inl (m : ℕ) (K : Type) [Field K] (b c : K)
    (w : Fin m ⊕ Fin m ⊕ Fin 2 → K) (i : Fin m) :
    (minusGram m K b c *ᵥ w) (Sum.inr (Sum.inl i)) = w (Sum.inl i) := by
  simp [Matrix.mulVec, dotProduct, minusGram, Fintype.sum_sum_type, Fin.sum_univ_two]

theorem minusGram_mulVec_uu (m : ℕ) (K : Type) [Field K] (b c : K)
    (w : Fin m ⊕ Fin m ⊕ Fin 2 → K) :
    (minusGram m K b c *ᵥ w) (Sum.inr (Sum.inr 0)) =
      2 * w (Sum.inr (Sum.inr 0)) + b * w (Sum.inr (Sum.inr 1)) := by
  simp [Matrix.mulVec, dotProduct, minusGram, Fintype.sum_sum_type, Fin.sum_univ_two]

theorem minusGram_mulVec_vv (m : ℕ) (K : Type) [Field K] (b c : K)
    (w : Fin m ⊕ Fin m ⊕ Fin 2 → K) :
    (minusGram m K b c *ᵥ w) (Sum.inr (Sum.inr 1)) =
      b * w (Sum.inr (Sum.inr 0)) + 2 * c * w (Sum.inr (Sum.inr 1)) := by
  simp [Matrix.mulVec, dotProduct, minusGram, Fintype.sum_sum_type, Fin.sum_univ_two]

theorem dotProduct_minusGram_mulVec (m : ℕ) (K : Type) [Field K] (b c : K)
    (v w : Fin m ⊕ Fin m ⊕ Fin 2 → K) :
    v ⬝ᵥ (minusGram m K b c *ᵥ w) =
      ∑ i : Fin m, (v (Sum.inl i) * w (Sum.inr (Sum.inl i)) +
          v (Sum.inr (Sum.inl i)) * w (Sum.inl i)) +
        (v (Sum.inr (Sum.inr 0)) * (2 * w (Sum.inr (Sum.inr 0)) + b * w (Sum.inr (Sum.inr 1))) +
          v (Sum.inr (Sum.inr 1)) * (b * w (Sum.inr (Sum.inr 0)) + 2 * c * w (Sum.inr (Sum.inr 1)))) := by
  simp only [dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, minusGram_mulVec_inl,
    minusGram_mulVec_inr_inl, minusGram_mulVec_uu, minusGram_mulVec_vv, Finset.sum_add_distrib]
  ring

theorem minusQuad_polar (m : ℕ) (K : Type) [Field K] (b c : K)
    (v w : Fin m ⊕ Fin m ⊕ Fin 2 → K) :
    minusQuadCore m K b c (v + w) =
      minusQuadCore m K b c v + minusQuadCore m K b c w + v ⬝ᵥ (minusGram m K b c *ᵥ w) := by
  rw [dotProduct_minusGram_mulVec]
  simp only [minusQuadCore, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
  have hcomm : ∑ x : Fin m, w (Sum.inl x) * v (Sum.inr (Sum.inl x)) =
      ∑ x : Fin m, v (Sum.inr (Sum.inl x)) * w (Sum.inl x) :=
    Finset.sum_congr rfl fun x _ => mul_comm _ _
  rw [hcomm]
  ring

theorem transpose_mul_gram_mul_of_isometry {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Q : (ι → K) → K) (Bm : Matrix ι ι K)
    (hpol : ∀ v w, Q (v + w) = Q v + Q w + v ⬝ᵥ (Bm *ᵥ w)) (A : Matrix ι ι K)
    (hA : ∀ v, Q (A *ᵥ v) = Q v) : Aᵀ * Bm * A = Bm := by
  have hB : ∀ v w, v ⬝ᵥ (Bm *ᵥ w) = Q (v + w) - Q v - Q w := fun v w => by
    rw [hpol]
    ring
  ext i j
  have hij : (Aᵀ * Bm * A) i j = (A *ᵥ Pi.single i 1) ⬝ᵥ (Bm *ᵥ (A *ᵥ Pi.single j 1)) := by
    rw [Matrix.mulVec_single_one, Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.mul_assoc]
    rfl
  rw [hij, hB, ← Matrix.mulVec_add]
  simp only [hA]
  rw [← hB]
  simp [Matrix.mulVec_single_one, single_dotProduct]

theorem isometryCore_preserves {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Q : (ι → K) → K) {A : GL ι K} (hA : A ∈ CFSG.MatrixModel.isometryCore Q) :
    ∀ v : ι → K, Q ((A : Matrix ι ι K) *ᵥ v) = Q v := by
  unfold CFSG.MatrixModel.isometryCore at hA
  induction hA using Subgroup.closure_induction with
  | mem x hx => exact fun v => hx v
  | one => intro v; simp
  | mul x y _ _ hx hy =>
    intro v
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hx, hy]
  | inv x _ hx =>
    intro v
    have h1 : (x : Matrix ι ι K) * ((x⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h := hx (((x⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v)
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] at h
    exact h.symm

theorem statedOmega_isometry {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Q : (ι → K) → K) {A : GL ι K} (hA : A ∈ StatedOmega Q) (v : ι → K) :
    Q ((A : Matrix ι ι K) *ᵥ v) = Q v := by
  have hle : StatedOmega Q ≤ CFSG.MatrixModel.isometryCore Q := by
    change ⁅CFSG.MatrixModel.isometryCore Q, CFSG.MatrixModel.isometryCore Q⁆ ≤ _
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg₁ hg₂) (inv_mem hg₁)) (inv_mem hg₂)
  exact isometryCore_preserves Q (hle hA) v

theorem minusGram_mulVec_eq_zero (m : ℕ) (K : Type) [Field K] (hodd : (2 : K) ≠ 0) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (v : Fin m ⊕ Fin m ⊕ Fin 2 → K)
    (hv : minusGram m K b c *ᵥ v = 0) : v = 0 := by
  have hA : ∀ i, v (Sum.inr (Sum.inl i)) = 0 := fun i => by
    have h := congrFun hv (Sum.inl i)
    rwa [minusGram_mulVec_inl, Pi.zero_apply] at h
  have hB : ∀ i, v (Sum.inl i) = 0 := fun i => by
    have h := congrFun hv (Sum.inr (Sum.inl i))
    rwa [minusGram_mulVec_inr_inl, Pi.zero_apply] at h
  have h3 : 2 * v (Sum.inr (Sum.inr 0)) + b * v (Sum.inr (Sum.inr 1)) = 0 := by
    have h := congrFun hv (Sum.inr (Sum.inr 0))
    rwa [minusGram_mulVec_uu, Pi.zero_apply] at h
  have h4 : b * v (Sum.inr (Sum.inr 0)) + 2 * c * v (Sum.inr (Sum.inr 1)) = 0 := by
    have h := congrFun hv (Sum.inr (Sum.inr 1))
    rwa [minusGram_mulVec_vv, Pi.zero_apply] at h
  have hd : 4 * c - b ^ 2 ≠ 0 := by
    intro h
    have h2 : (2 : K) * 2⁻¹ = 1 := mul_inv_cancel₀ hodd
    exact hirr (-b * 2⁻¹)
      (by linear_combination (2⁻¹ : K) ^ 2 * h + (b ^ 2 * 2⁻¹ - c - 2 * c * 2⁻¹) * h2)
  have hu : v (Sum.inr (Sum.inr 0)) = 0 :=
    (mul_eq_zero.mp (show (4 * c - b ^ 2) * v (Sum.inr (Sum.inr 0)) = 0 by
      linear_combination (2 * c) * h3 - b * h4)).resolve_left hd
  have hw : v (Sum.inr (Sum.inr 1)) = 0 :=
    (mul_eq_zero.mp (show (4 * c - b ^ 2) * v (Sum.inr (Sum.inr 1)) = 0 by
      linear_combination 2 * h4 - b * h3)).resolve_left hd
  funext r
  rcases r with i | i | k
  · simpa using hB i
  · simpa using hA i
  · fin_cases k
    · simpa using hu
    · simpa using hw

theorem minusGram_isUnit_det (m : ℕ) (K : Type) [Field K] (hodd : (2 : K) ≠ 0) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : IsUnit (minusGram m K b c).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hmv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  exact hv0 (minusGram_mulVec_eq_zero m K hodd b c hirr v hmv)

end CFSG.ComponentClassification.CatFC.KGHS3
