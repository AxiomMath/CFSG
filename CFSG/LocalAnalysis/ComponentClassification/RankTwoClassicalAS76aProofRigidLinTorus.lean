module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofRigidLinPsi

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin (perfectCore)
open scoped commutatorElement

section MidSL

variable {K : Type} [Field K] {k : ℕ}

theorem det_midEmbed (hk : 2 ≤ k) (A : Matrix (StdMid hk) (StdMid hk) K) :
    (midEmbed K hk A).det = A.det := by
  change (Matrix.reindex _ _ (fromBlocks A 0 0 (1 : Matrix (StdEnds hk) (StdEnds hk) K))).det =
    A.det
  rw [det_reindex_self, det_fromBlocks_zero₂₁, det_one, mul_one]

variable (K) in
@[expose] noncomputable def midSL (hk : 2 ≤ k) :
    SpecialLinearGroup (StdMid hk) K →* SpecialLinearGroup (Fin (2 + k)) K where
  toFun A := ⟨midEmbed K hk (A : Matrix (StdMid hk) (StdMid hk) K), by
    rw [det_midEmbed]; exact A.2⟩
  map_one' := Subtype.ext (by
    change midEmbed K hk ((1 : SpecialLinearGroup (StdMid hk) K) :
      Matrix (StdMid hk) (StdMid hk) K) = 1
    rw [Matrix.SpecialLinearGroup.coe_one, map_one])
  map_mul' A B := Subtype.ext (by
    change midEmbed K hk ((A * B : SpecialLinearGroup (StdMid hk) K) :
      Matrix (StdMid hk) (StdMid hk) K) = midEmbed K hk (A : Matrix (StdMid hk) (StdMid hk) K) *
        midEmbed K hk (B : Matrix (StdMid hk) (StdMid hk) K)
    rw [Matrix.SpecialLinearGroup.coe_mul, map_mul])

theorem mul_single_uv_of_col (hk : 2 ≤ k) {M : Matrix (Fin (2 + k)) (Fin (2 + k)) K}
    (hM : ∀ x, M x (idxU hk) = (1 : Matrix (Fin (2 + k)) (Fin (2 + k)) K) x (idxU hk)) :
    M * single (idxU hk) (idxV hk) 1 = single (idxU hk) (idxV hk) 1 := by
  ext x y
  rw [Matrix.mul_apply, Finset.sum_eq_single (idxU hk)
    (fun t _ ht => mul_eq_zero_of_right _ (single_apply_of_row_ne (Ne.symm ht) _ _ _))
    (fun h => absurd (Finset.mem_univ _) h)]
  simp only [hM, one_apply, single_apply]
  by_cases hx : x = idxU hk <;> by_cases hy : y = idxV hk <;> simp [hx, hy, eq_comm]

theorem single_uv_mul_of_row (hk : 2 ≤ k) {M : Matrix (Fin (2 + k)) (Fin (2 + k)) K}
    (hM : ∀ y, M (idxV hk) y = (1 : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (idxV hk) y) :
    single (idxU hk) (idxV hk) 1 * M = single (idxU hk) (idxV hk) 1 := by
  ext x y
  rw [Matrix.mul_apply, Finset.sum_eq_single (idxV hk)
    (fun t _ ht => mul_eq_zero_of_left (single_apply_of_col_ne _ _ (Ne.symm ht) _) _)
    (fun h => absurd (Finset.mem_univ _) h)]
  simp only [hM, one_apply, single_apply]
  by_cases hx : x = idxU hk <;> by_cases hy : y = idxV hk <;> simp [hx, hy, eq_comm]

theorem midSL_range_le_perfectCore (hk : 2 ≤ k) (h4 : ∃ s : Finset K, s.card = 4) :
    (midSL K hk).range ≤ perfectCore (stdCen K hk) := by
  refine CFSG.Quasithin.le_perfectCore_of_perfect ?_
    (commutator_range_of_perfect _ (isQuasisimple_SL_stdMid hk h4).1.commutator_eq_top)
  rintro _ ⟨A, rfl⟩
  rw [stdCen, mem_centralizer_singleton_iff]
  apply Subtype.ext
  change midEmbed K hk (A : Matrix (StdMid hk) (StdMid hk) K) * (1 + single _ _ 1) =
    (1 + single _ _ 1) * midEmbed K hk (A : Matrix (StdMid hk) (StdMid hk) K)
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
    mul_single_uv_of_col hk fun x => midEmbed_apply_of_end hk _ (Or.inr fun h => h.1 rfl),
    single_uv_mul_of_row hk fun y => midEmbed_apply_of_end hk _ (Or.inl fun h => h.2 rfl)]

theorem mem_range_midSL_of_apply (hk : 2 ≤ k) {g : SpecialLinearGroup (Fin (2 + k)) K}
    (hg : ∀ x y : Fin (2 + k), (¬ (x ≠ idxU hk ∧ x ≠ idxV hk) ∨ ¬ (y ≠ idxU hk ∧ y ≠ idxV hk)) →
      (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) x y =
        (1 : Matrix (Fin (2 + k)) (Fin (2 + k)) K) x y) :
    g ∈ (midSL K hk).range := by
  have heq : (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
      midEmbed K hk (stdRhoMat hk (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K)) := by
    ext x y
    by_cases hx : x ≠ idxU hk ∧ x ≠ idxV hk
    · by_cases hy : y ≠ idxU hk ∧ y ≠ idxV hk
      · have h := midEmbed_apply_mid hk (stdRhoMat hk (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K))
          ⟨x, hx⟩ ⟨y, hy⟩
        dsimp only at h
        rw [h]
        rfl
      · rw [hg x y (Or.inr hy), midEmbed_apply_of_end hk _ (Or.inr hy)]
    · rw [hg x y (Or.inl hx), midEmbed_apply_of_end hk _ (Or.inl hx)]
  have hdet : (stdRhoMat hk (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K)).det = 1 := by
    have h := g.2
    rwa [heq, det_midEmbed] at h
  exact ⟨⟨stdRhoMat hk (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K), hdet⟩, Subtype.ext heq.symm⟩

end MidSL

section Torus

variable {K : Type} [Field K] {k : ℕ}

@[expose] def linTorusDiag (hk : 3 ≤ k) (l : K) : Fin k → K :=
  fun j => if j = ⟨2, by omega⟩ then l⁻¹ ^ 2 else 1

variable (K) in
@[expose] noncomputable def linTorus (hk : 3 ≤ k) {l : K} (hl : l ≠ 0) :
    SpecialLinearGroup (Fin (2 + k)) K :=
  ⟨blk (l • 1) (diagonal (linTorusDiag hk l)), by
    rw [det_blk, det_smul, det_one, mul_one, Fintype.card_fin, det_diagonal,
      Finset.prod_eq_single (⟨2, by omega⟩ : Fin k) (fun j _ hj => by
        rw [linTorusDiag, ite_eq_right hj]) (fun h => absurd (Finset.mem_univ _) h),
      linTorusDiag, ite_eq_left rfl, ← mul_pow, mul_inv_cancel₀ hl, one_pow]⟩

theorem coe_linTorus (hk : 3 ≤ k) {l : K} (hl : l ≠ 0) :
    ((linTorus K hk hl : SpecialLinearGroup (Fin (2 + k)) K) :
      Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
      diagonal (Sum.elim (fun _ => l) (linTorusDiag hk l) ∘ finSumFinEquiv.symm) := by
  change blk (l • 1) (diagonal (linTorusDiag hk l)) = _
  rw [blk, smul_one_eq_diagonal, fromBlocks_diagonal, coe_reindexAlgEquiv, reindex_apply,
    submatrix_diagonal_equiv]

theorem linTorus_commute_blkSL₁ (hk : 3 ≤ k) {l : K} (hl : l ≠ 0)
    (X : SpecialLinearGroup (Fin 2) K) :
    linTorus K hk hl * blkSL₁ X = blkSL₁ X * linTorus K hk hl := by
  apply Subtype.ext
  change blk (l • 1) (diagonal (linTorusDiag hk l)) * blk (X : Matrix (Fin 2) (Fin 2) K) 1 =
    blk (X : Matrix (Fin 2) (Fin 2) K) 1 * blk (l • 1) (diagonal (linTorusDiag hk l))
  rw [blk_mul, blk_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_one, Matrix.one_mul]

theorem linTorus_mem_perfectCore (hk : 3 ≤ k) (h4 : ∃ s : Finset K, s.card = 4) {l : K}
    (hl : l ≠ 0) : linTorus K hk hl ∈ perfectCore (stdCen K (by omega : 2 ≤ k)) := by
  refine midSL_range_le_perfectCore (by omega) h4 (mem_range_midSL_of_apply _ fun x y hxy => ?_)
  rw [coe_linTorus, diagonal_apply, one_apply]
  split_ifs with hxy'
  · subst hxy'
    have hx : x = idxU (by omega : 2 ≤ k) ∨ x = idxV (by omega : 2 ≤ k) := by
      rcases hxy with h | h <;> push Not at h <;> by_contra hc <;> push Not at hc <;>
        exact absurd (h hc.1) hc.2
    rcases hx with rfl | rfl
    · rw [idxU, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr, linTorusDiag,
        ite_eq_right (by simp [Fin.ext_iff])]
    · rw [idxV, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr, linTorusDiag,
        ite_eq_right (by simp [Fin.ext_iff])]
  · rfl

theorem midTorusShape_linTorus (hk : 3 ≤ k) {l : K} (hl : l ≠ 0) :
    MidTorusShape (by omega : 2 ≤ k) l (stdRhoMat (by omega : 2 ≤ k)
      ((linTorus K hk hl : SpecialLinearGroup (Fin (2 + k)) K) :
        Matrix (Fin (2 + k)) (Fin (2 + k)) K)) := by
  intro a b hab
  rw [stdRhoMat, submatrix_apply, coe_linTorus, diagonal_apply]
  have hB : ∀ x : Fin (2 + k), IsBlockOne k x →
      (Sum.elim (fun _ => l) (linTorusDiag hk l) ∘ finSumFinEquiv.symm) x = l := by
    rintro x (rfl | rfl) <;> simp [idxW, idxW']
  by_cases h : a = b
  · subst h
    rw [ite_eq_left rfl, ite_eq_left rfl]
    rcases hab with ha | ha <;> exact hB _ ha
  · rw [ite_eq_right (fun h' => h (Subtype.ext h')), ite_eq_right h]

end Torus

end CFSG.ComponentClassification.RankTwoClassical
