module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Basic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance.Sp

open CFSG.ClassicalInvolution.Models.SymplecticPairs
open scoped Matrix

variable {F : Type} [Field F]

theorem map_transvection {ι : Type*} [DecidableEq ι] [Fintype ι] (σ : F ≃+* F) (p q : ι)
    (c : F) : (Matrix.transvection p q c).map σ = Matrix.transvection p q (σ c) := by
  ext r t
  simp only [Matrix.transvection, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  split_ifs <;> simp

theorem rigid_transvection {ι : Type*} [DecidableEq ι] [Fintype ι] (σ : F ≃+* F)
    {Am B : Matrix ι ι F} (hAB : Am * B = 1) (p q : ι)
    (h : ∀ c : F, Am * (Matrix.transvection p q c).map σ = Matrix.transvection p q c * Am) :
    (∀ c, σ c = c) ∧ Am * Matrix.single p q (1 : F) = Matrix.single p q 1 * Am := by
  have hmul : ∀ c : F, Am * Matrix.single p q (σ c) = Matrix.single p q c * Am := by
    intro c
    have := h c
    rw [map_transvection] at this
    simp only [Matrix.transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.one_mul] at this
    exact add_left_cancel this
  have h1 : Am * Matrix.single p q (1 : F) = Matrix.single p q 1 * Am := by
    simpa using hmul 1
  have hrow : ∀ t, t ≠ q → Am q t = 0 := by
    intro t ht
    have := congrFun (congrFun h1 p) t
    rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ ht, Matrix.single_mul_apply_same] at this
    simpa using this.symm
  have hdiag : Am p p = Am q q := by
    have := congrFun (congrFun h1 p) q
    rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_same] at this
    simpa using this
  have hne : Am q q ≠ 0 := by
    intro h0
    have := congrFun (congrFun hAB q) q
    rw [Matrix.mul_apply, Finset.sum_eq_single q] at this
    · rw [h0, zero_mul] at this
      simp at this
    · intro t _ ht
      rw [hrow t ht, zero_mul]
    · simp
  refine ⟨fun c => ?_, h1⟩
  have := congrFun (congrFun (hmul c) p) q
  rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_same, hdiag] at this
  exact mul_left_cancel₀ hne (by linear_combination this)

theorem exists_diagonal_of_commute {Am : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (hU : ∀ a : Fin 2, Am * Matrix.single (Sum.inl a) (Sum.inr a) (1 : F) =
      Matrix.single (Sum.inl a) (Sum.inr a) 1 * Am)
    (hL : ∀ a : Fin 2, Am * Matrix.single (Sum.inr a) (Sum.inl a) (1 : F) =
      Matrix.single (Sum.inr a) (Sum.inl a) 1 * Am) :
    ∃ u : Fin 2 → F, Am = Matrix.diagonal (Sum.elim u u) := by
  have hl : ∀ (a : Fin 2) (r : Fin 2 ⊕ Fin 2), r ≠ Sum.inl a → Am r (Sum.inl a) = 0 := by
    intro a r hr
    have := congrFun (congrFun (hU a) r) (Sum.inr a)
    rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne (h := hr)] at this
    simpa using this
  have hr' : ∀ (a : Fin 2) (r : Fin 2 ⊕ Fin 2), r ≠ Sum.inr a → Am r (Sum.inr a) = 0 := by
    intro a r hr
    have := congrFun (congrFun (hL a) r) (Sum.inl a)
    rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne (h := hr)] at this
    simpa using this
  have hd : ∀ a : Fin 2, Am (Sum.inl a) (Sum.inl a) = Am (Sum.inr a) (Sum.inr a) := by
    intro a
    have := congrFun (congrFun (hU a) (Sum.inl a)) (Sum.inr a)
    rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_same] at this
    simpa using this
  refine ⟨fun a => Am (Sum.inl a) (Sum.inl a), ?_⟩
  ext r t
  rw [Matrix.diagonal_apply]
  rcases t with a | a
  · by_cases h : r = Sum.inl a
    · subst h
      simp
    · simp [h, hl a r h]
  · by_cases h : r = Sum.inr a
    · subst h
      simp [hd a]
    · simp [h, hr' a r h]

theorem sq_eq_of_similitude {u : Fin 2 → F} {μ : F}
    (h : (Matrix.diagonal (Sum.elim u u))ᵀ * gram F 2 * Matrix.diagonal (Sum.elim u u) =
      μ • gram F 2) (a : Fin 2) : u a * u a = μ := by
  have := congrFun (congrFun h (Sum.inl a)) (Sum.inr a)
  rw [transpose_mul_gram_mul_apply, Finset.sum_eq_single (Sum.inl a)] at this
  · simpa [gram_apply, sgn, par] using this
  · intro b _ hb
    simp [Matrix.diagonal_apply, hb]
  · simp

end CFSG.ClassicalInvolution.Balance.StrongBalance.Sp
