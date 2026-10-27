module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidQE

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ORigid

open Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open scoped MatrixGroups

section Avec

variable {K : Type} [Field K] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂] [Fintype ι]
  [DecidableEq ι] (oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι)

@[expose] def avec₂ (g : Matrix ι ι K) : Fin 2 → ι₂ → K := fun t a => g (ou oe a) (oy oe t)

@[expose] def fBlk (g : Matrix ι ι K) : Matrix (Fin 2) (Fin 2) K :=
  fun r t => g (oy oe r) (oy oe t)

variable {oe}

omit [DecidableEq ι₂] [DecidableEq ι] in
theorem avec₂_mul {g : Matrix ι ι K} (hg : ∀ a r, g (ou oe a) (ox oe r) = 0) (h : Matrix ι ι K)
    (t : Fin 2) :
    avec₂ oe (g * h) t = uBlk oe g *ᵥ avec₂ oe h t + ∑ r, h (oy oe r) (oy oe t) • avec₂ oe g r := by
  funext a
  have h1 : ∀ r, g (ou oe a) (ox oe r) = 0 := hg a
  simp only [avec₂, Matrix.mul_apply, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, mulVec, dotProduct, uBlk]
  rw [sum_oe oe]
  simp only [h1, zero_mul, Finset.sum_const_zero, zero_add]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

omit [DecidableEq ι₂] [DecidableEq ι] in
theorem fBlk_mul {g : Matrix ι ι K} (hg : IsEShape oe g) (h : Matrix ι ι K) :
    fBlk oe (g * h) = fBlk oe g * fBlk oe h := by
  ext r t
  have h1 : ∀ a, g (oy oe r) (ou oe a) = 0 := fun a => hg.2 _ (ou_ne_oy oe a) r
  have h2 : ∀ s, g (oy oe r) (ox oe s) = 0 := fun s => hg.2 _ (ox_ne_oy oe s) r
  simp only [fBlk, Matrix.mul_apply]
  rw [sum_oe oe]
  simp [h1, h2]

omit [Fintype ι₂] [DecidableEq ι₂] in
theorem avec₂_qE (Q₂ : QuadraticForm K (ι₂ → K)) (u : Fin 2 → ι₂ → K) (c : K) :
    avec₂ oe (qE oe Q₂ u c) = u := by
  funext t a
  rw [avec₂, qE_apply, qE_mulVec_ou]
  simp [Pi.single_apply]

omit [Fintype ι₂] [DecidableEq ι₂] in
theorem fBlk_qE (Q₂ : QuadraticForm K (ι₂ → K)) (u : Fin 2 → ι₂ → K) (c : K) :
    fBlk oe (qE oe Q₂ u c) = 1 := by
  ext r t
  rw [fBlk, qE_apply, qE_mulVec_oy, Matrix.one_apply]
  simp [Pi.single_apply]

end Avec

section Oblk

variable {K : Type} [Field K] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂] [Fintype ι]
  [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι}

theorem oblk_ou_ou (Y : Matrix ι₂ ι₂ K) (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (a b : ι₂) : oblk oe Y X (ou oe a) (ou oe b) = Y a b := by
  rw [oblk_apply]
  rfl

theorem oblk_ou_inr (Y : Matrix ι₂ ι₂ K) (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (a : ι₂) (c : Fin 2 ⊕ Fin 2) : oblk oe Y X (ou oe a) (oe (.inr c)) = 0 := by
  rw [oblk_apply]
  rfl

theorem oblk_inr_ou (Y : Matrix ι₂ ι₂ K) (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (c : Fin 2 ⊕ Fin 2) (a : ι₂) : oblk oe Y X (oe (.inr c)) (ou oe a) = 0 := by
  rw [oblk_apply]
  rfl

theorem oblk_inr_inr (Y : Matrix ι₂ ι₂ K) (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (c d : Fin 2 ⊕ Fin 2) : oblk oe Y X (oe (.inr c)) (oe (.inr d)) = X c d := by
  rw [oblk_apply]
  rfl

theorem eBlk_oblk (Y : Matrix ι₂ ι₂ K) (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :
    eBlk oe (oblk oe Y X) = fun s t => X (.inl s) (.inl t) := by
  funext s t
  exact oblk_inr_inr Y X _ _

theorem uBlk_oblk (Y : Matrix ι₂ ι₂ K) (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :
    uBlk oe (oblk oe Y X) = Y := by
  funext a b
  exact oblk_ou_ou Y X a b

theorem avec₂_oblk (Y : Matrix ι₂ ι₂ K) (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :
    avec₂ oe (oblk oe Y X) = 0 := by
  funext t a
  exact oblk_ou_inr Y X a _

theorem avec₂_oblk_mul_mul (Y Y' : Matrix ι₂ ι₂ K)
    (X X' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) {q : Matrix ι ι K}
    (hq : ∀ a r, q (ou oe a) (ox oe r) = 0) (t : Fin 2) :
    avec₂ oe (oblk oe Y X * q * oblk oe Y' X') t =
      Y *ᵥ ∑ r, X' (.inr r) (.inr t) • avec₂ oe q r := by
  have hb : ∀ (Z : Matrix ι₂ ι₂ K) (W : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) a r,
      oblk oe Z W (ou oe a) (ox oe r) = 0 := fun Z W a r => oblk_ou_inr Z W a _
  have h0 : ∀ r, (oblk oe Y' X') (oy oe r) (oy oe t) = X' (.inr r) (.inr t) := fun r =>
    oblk_inr_inr _ _ _ _
  rw [Matrix.mul_assoc, avec₂_mul (hb Y X), avec₂_mul hq, uBlk_oblk, avec₂_oblk, avec₂_oblk]
  simp [h0]

end Oblk

section Rho

variable {K : Type} [Field K]

theorem rhoTwoMat_inv_inr_inr (A : SL(2, K)) (r t : Fin 2) :
    rhoTwoMat A⁻¹ (.inr r) (.inr t) = (A : Matrix (Fin 2) (Fin 2) K) t r := by
  rw [rhoTwoMat_apply, fromBlocks_apply₂₂, transpose_apply,
    Matrix.SpecialLinearGroup.coe_inv, adjugate_adjugate _ (by simp)]
  simp

end Rho

end CFSG.ComponentClassification.RankTwoClassical.ORigid
