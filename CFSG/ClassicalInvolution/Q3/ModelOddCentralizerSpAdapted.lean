module

public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerComplexBasis
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerSpGauss
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Pairs

public section

namespace CFSG.ClassicalInvolution.Q3

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)

section Family

variable {F : Type} [Field F] {n : ℕ}

@[expose] def colMat (v : Fin n ⊕ Fin n → Fin n ⊕ Fin n → F) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
  Matrix.of fun r c => v c r

theorem colMat_symplectic {v : Fin n ⊕ Fin n → Fin n ⊕ Fin n → F}
    (hv : ∀ x y, form (v x) (v y) = gram F n x y) :
    (colMat v)ᵀ * gram F n * colMat v = gram F n := by
  ext x y
  rw [transpose_mul_gram_mul_apply, ← hv x y, form_apply]
  rfl

theorem det_ne_zero_of_mul_eq_one {ι : Type} [Fintype ι] [DecidableEq ι]
    {M N : Matrix ι ι F} (h : M * N = 1) : M.det ≠ 0 := by
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at this
  exact left_ne_zero_of_mul_eq_one this

end Family

section Complex

variable {F : Type} [Field F] [Finite F] [hF3 : Fact (Nat.card F = 3)] {n : ℕ}

theorem exists_sq_add_sq_mul_eq_one' (c : F) (hc : c ≠ 0) :
    ∃ a b : F, (a ^ 2 + b ^ 2) * c = 1 := by
  have : Fintype F := Fintype.ofFinite F
  have h1 := FiniteField.pow_card_sub_one_eq_one c hc
  rw [← Nat.card_eq_fintype_card, hF3.out] at h1
  have hc2 : c * c = 1 := by simpa [pow_two] using h1
  have h3 : (3 : F) = 0 := by
    have := charP_of_card_eq_three (F := F)
    exact_mod_cast CharP.cast_eq_zero F 3
  rcases mul_self_eq_one_iff.mp hc2 with h | h
  · exact ⟨1, 0, by rw [h]; ring⟩
  · exact ⟨1, 1, by rw [h]; linear_combination (-1 : F) * h3⟩

theorem exists_conj_gComplex (g : StatedSp n F) (hg : mat n F g * mat n F g = -1) :
    ∃ Q : StatedSp n F, g * Q = Q * gComplex n := by
  set G := mat n F g with hG
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_odd_natCard
    (by rw [hF3.out]; decide)
  let _ : Invertible (2 : F) := invertibleOfNonzero h2
  let gl : (Fin n ⊕ Fin n → F) →ₗ[F] (Fin n ⊕ Fin n → F) := Matrix.mulVecLin G
  let β : LinearMap.BilinForm F (Fin n ⊕ Fin n → F) := Matrix.toBilin' (gram F n * G)
  have hβ : ∀ x y, β x y = form x (G *ᵥ y) := fun x y => by
    rw [Matrix.toBilin'_apply', ← Matrix.mulVec_mulVec]
    rfl
  have hGG : ∀ x, G *ᵥ (G *ᵥ x) = -x := fun x => by
    rw [Matrix.mulVec_mulVec, hg, Matrix.neg_mulVec, Matrix.one_mulVec]
  have hform : ∀ x y, form (G *ᵥ x) (G *ᵥ y) = form x y := form_mulVec g
  have hneg : ∀ u y : Fin n ⊕ Fin n → F, form u (-y) = -form u y := fun u y => by
    simp [form, Matrix.mulVec_neg, dotProduct_neg]
  have hsymm : β.IsSymm := ⟨fun x y => by
    rw [hβ, hβ]
    calc form x (G *ᵥ y) = form (G *ᵥ x) (G *ᵥ (G *ᵥ y)) := (hform _ _).symm
      _ = form (G *ᵥ x) (-y) := by rw [hGG]
      _ = form y (G *ᵥ x) := by rw [hneg, form_antisymm (G *ᵥ x) y]⟩
  have hnd : β.Nondegenerate := by
    refine Matrix.nondegenerate_toBilin'_iff.2 (Matrix.nondegenerate_iff_det_ne_zero.2 ?_)
    rw [Matrix.det_mul]
    refine mul_ne_zero (det_ne_zero_of_mul_eq_one (N := -gram F n) ?_)
      (det_ne_zero_of_mul_eq_one (N := -G) ?_)
    · rw [Matrix.mul_neg, gram_mul_gram, neg_neg]
    · rw [Matrix.mul_neg, hg, neg_neg]
  have hgβ : ∀ x y, β (gl x) (gl y) = β x y := fun x y => by
    rw [hβ, hβ]
    exact hform _ _
  have hdim : Module.finrank F (Fin n ⊕ Fin n → F) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  obtain ⟨e, hee, hge⟩ := exists_adapted_family exists_sq_add_sq_mul_eq_one' n β gl hsymm hnd
    (fun x => hGG x) hgβ hdim
  have hf0 : ∀ x y : Fin n ⊕ Fin n → F, form x y = -β x (G *ᵥ y) := fun x y => by
    rw [hβ, hGG, hneg, neg_neg]
  have hee' : ∀ k l, form (e k) (G *ᵥ e l) = if k = l then 1 else 0 := fun k l => by
    rw [← hβ]
    exact hee k l
  have hff : ∀ k l, form (e k) (e l) = 0 := fun k l => by
    rw [hf0]
    have := hge k l
    rw [show gl (e l) = G *ᵥ e l from rfl] at this
    rw [this, neg_zero]
  set v : Fin n ⊕ Fin n → Fin n ⊕ Fin n → F := Sum.elim e (fun k => G *ᵥ e k) with hv
  have hvv : ∀ x y, form (v x) (v y) = gram F n x y := by
    rintro (k | k) (l | l)
    · simp only [hv, Sum.elim_inl]
      rw [hff]
      simp [Models.SymplecticPairs.gram]
    · simp only [hv, Sum.elim_inl, Sum.elim_inr]
      rw [hee']
      simp [Models.SymplecticPairs.gram, Matrix.one_apply]
    · simp only [hv, Sum.elim_inl, Sum.elim_inr]
      rw [form_antisymm (e l) (G *ᵥ e k), hee']
      simp [Models.SymplecticPairs.gram, Matrix.one_apply, eq_comm]
    · simp only [hv, Sum.elim_inr]
      rw [hform, hff]
      simp [Models.SymplecticPairs.gram]
  refine ⟨ofSymplecticMat (colMat v) (colMat_symplectic hvv), mat_injective ?_⟩
  rw [map_mul, map_mul, mat_ofSymplecticMat, ← hG]
  have hgc : mat n F (gComplex n) = Matrix.fromBlocks 0 (-1) 1 0 := mat_ofSymplecticMat _ _
  rw [hgc]
  set Jc : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F := Matrix.fromBlocks 0 (-1) 1 0 with hJc
  refine Matrix.ext fun r c => ?_
  rcases c with k | k
  · have h1 : (G * colMat v) r (Sum.inl k) = (G *ᵥ e k) r := by
      simp [colMat, hv, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    have h2 : (colMat v * Jc) r (Sum.inl k) = (G *ᵥ e k) r := by
      simp [colMat, hv, hJc, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
    rw [h1, h2]
  · have h1 : (G * colMat v) r (Sum.inr k) = -e k r := by
      have : (G * colMat v) r (Sum.inr k) = (G *ᵥ (G *ᵥ e k)) r := by
        simp [colMat, hv, Matrix.mul_apply, Matrix.mulVec, dotProduct]
      rw [this, hGG]
      rfl
    have h2 : (colMat v * Jc) r (Sum.inr k) = -e k r := by
      simp [colMat, hv, hJc, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
    rw [h1, h2]

end Complex

end CFSG.ClassicalInvolution.Q3
