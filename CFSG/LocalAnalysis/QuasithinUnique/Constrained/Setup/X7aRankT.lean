module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aKron
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aInvol
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aIrred

public section

namespace CFSG.QuasithinUnique.Setup.X7a

open scoped MatrixGroups Matrix

section Local

variable {F : Type} [Field F] [CharP F 2] (k : Type) [Field k] [Algebra F k] [CharP k 2]

@[expose] def adjT0 : Matrix (Fin 8) (Fin 8) k :=
  !![1, 1, 0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 1, 1, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1, 0, 0; 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 0, 1]

omit [CharP F 2] in
theorem twistMat_tr0 (i : ℕ) : twistMat k i (up3 (0 : F) 0 1) = upMat (0 : k) 0 1 := by
  rw [twistMat_up3]
  simp [map_zero, map_one]

omit [CharP F 2] in
theorem natRep_tr0 (i : ℕ) : natRep k i (up3 (0 : F) 0 1) = !![1, 1, 0; 0, 1, 0; 0, 0, 1] := by
  rw [natRep_apply, twistMat_tr0]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [upMat]

theorem up3_001_inv : (up3 (0 : F) 0 1)⁻¹ = up3 0 0 1 := by
  rw [up3_inv]
  simp

theorem dualRep_tr0 (i : ℕ) : dualRep k i (up3 (0 : F) 0 1) = !![1, 0, 0; 1, 1, 0; 0, 0, 1] := by
  rw [dualRep_apply, up3_001_inv, twistMat_tr0]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [upMat]

theorem adjRep_tr0 (i : ℕ) : adjRep k i (up3 (0 : F) 0 1) = adjT0 k := by
  have h2 : (1 : k) + 1 = 0 := CharTwo.add_self_eq_zero (1 : k)
  ext r s
  rw [adjRep_apply, conjMat, up3_001_inv, twistMat_tr0]
  fin_cases r <;> fin_cases s <;>
    simp [co, Xm, upMat, adjT0, Matrix.mul_apply, Fin.sum_univ_three, h2]

end Local

section Split

variable {F : Type} [Field F] (k : Type) [Field k] [Algebra F k] [CharP k 2] {ι : Type}
  [Fintype ι] [DecidableEq ι]

@[expose] def splitIdxGen (τ : ι → Bool × Bool) (p : ι) :
    (∀ i, Fin (locDim (τ i).1 (τ i).2)) ≃
      (∀ j : {j : ι // j ≠ p}, Fin (locDim (τ j).1 (τ j).2)) × Fin (locDim (τ p).1 (τ p).2) :=
  (Equiv.piSplitAt p _).trans (Equiv.prodComm _ _)

theorem tensorRepGen_rank_split (τ : ι → Bool × Bool) (e : ι → ℕ) (p : ι) (ℓ : Bool × Bool)
    (hℓ : τ p = ℓ) (g : SL(3, F)) :
    (tensorRepGen k τ e g - 1).rank =
      (Matrix.kroneckerMap (· * ·)
        (tensorRepGen k (fun j : {j : ι // j ≠ p} => τ j) (fun j => e j) g)
        (locRep k ℓ.1 ℓ.2 (e p) g) - 1).rank := by
  subst hℓ
  have hh : ∀ x' x, Matrix.kroneckerMap (· * ·)
      (tensorRepGen k (fun j : {j : ι // j ≠ p} => τ j) (fun j => e j) g)
      (locRep k (τ p).1 (τ p).2 (e p) g) (splitIdxGen τ p x') (splitIdxGen τ p x) =
      tensorRepGen k τ e g x' x := by
    intro x' x
    simp only [Matrix.kroneckerMap_apply]
    show tensorRepGen k (fun j : {j : ι // j ≠ p} => τ j) (fun j => e j) g (fun j => x' j)
      (fun j => x j) * locRep k (τ p).1 (τ p).2 (e p) g (x' p) (x p) =
        tensorRepGen k τ e g x' x
    rw [tensorRepGen_apply, tensorRepGen_apply, Fintype.prod_eq_mul_prod_subtype_ne _ p, mul_comm]
  have : tensorRepGen k τ e g - 1 = (Matrix.kroneckerMap (· * ·)
      (tensorRepGen k (fun j : {j : ι // j ≠ p} => τ j) (fun j => e j) g)
      (locRep k (τ p).1 (τ p).2 (e p) g) - 1).submatrix (splitIdxGen τ p) (splitIdxGen τ p) := by
    ext x' x
    simp only [Matrix.sub_apply, Matrix.submatrix_apply, Matrix.one_apply, hh,
      (splitIdxGen τ p).apply_eq_iff_eq]
  rw [this, Matrix.rank_submatrix]

omit [CharP k 2] in
theorem rank_kron_unit {α : Type} [Fintype α] [DecidableEq α] (R : Matrix α α k) :
    (Matrix.kroneckerMap (· * ·) R (1 : Matrix (Fin 1) (Fin 1) k) - 1).rank = (R - 1).rank := by
  have : Matrix.kroneckerMap (· * ·) R (1 : Matrix (Fin 1) (Fin 1) k) - 1 =
      (R - 1).submatrix (Equiv.prodUnique α (Fin 1)) (Equiv.prodUnique α (Fin 1)) := by
    ext ⟨x, a⟩ ⟨y, b⟩
    have hab : a = b := Subsingleton.elim _ _
    subst hab
    simp [Matrix.one_apply]
  rw [this, Matrix.rank_submatrix]

end Split

section Main

variable {F : Type} [Field F] [CharP F 2] (k : Type) [Field k] [Algebra F k] [CharP k 2]

omit [CharP F 2] [CharP k 2] in
theorem adjT0_free : ∀ c : Fin 8 → k, (∀ b ∉ ({1, 2, 5, 7} : Finset (Fin 8)), c b = 0) →
    (∀ i ∉ ({1, 2, 5, 7} : Finset (Fin 8)), ∑ b, adjT0 k i b * c b = 0) → c = 0 := by
  intro c hc hi
  have h0 := hc 0 (by decide)
  have h3 := hc 3 (by decide)
  have h4 := hc 4 (by decide)
  have h6 := hc 6 (by decide)
  have e0 := hi 0 (by decide)
  have e3 := hi 3 (by decide)
  have e4 := hi 4 (by decide)
  have e6 := hi 6 (by decide)
  simp [adjT0, Fin.sum_univ_succ] at e0 e3 e4 e6
  funext b
  fin_cases b <;> simp_all

theorem dim_le_two_mul_rank_add_one : ∀ (n : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι],
    Fintype.card ι = n → ∀ (τ : ι → Bool × Bool) (e : ι → ℕ),
      ∏ i, locDim (τ i).1 (τ i).2 ≤
        2 * (tensorRepGen (F := F) k τ e (up3 (0 : F) 0 1) - 1).rank + 1 := by
  intro n
  induction n with
  | zero =>
    intro ι _ _ hcard τ e
    have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hcard
    simp
  | succ n ih =>
    intro ι _ _ hcard τ e
    obtain ⟨p⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    have hrest : Fintype.card {j : ι // j ≠ p} = n := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
      omega
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Bool × Bool, τ p = ℓ := ⟨_, rfl⟩
    have hprod : ∏ i, locDim (τ i).1 (τ i).2 =
        locDim ℓ.1 ℓ.2 * ∏ j : {j : ι // j ≠ p}, locDim (τ j).1 (τ j).2 := by
      rw [Fintype.prod_eq_mul_prod_subtype_ne _ p, hℓ]
    rw [hprod, tensorRepGen_rank_split k τ e p ℓ hℓ]
    have ihR := ih hrest (fun j : {j : ι // j ≠ p} => τ j) (fun j => e j)
    have hRR' : tensorRepGen (F := F) k (fun j : {j : ι // j ≠ p} => τ j) (fun j => e j)
        (up3 (0 : F) 0 1) *
        tensorRepGen (F := F) k (fun j : {j : ι // j ≠ p} => τ j) (fun j => e j)
          (up3 (0 : F) 0 1)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have hcardα : Fintype.card (∀ j : {j : ι // j ≠ p}, Fin (locDim (τ j).1 (τ j).2)) =
        ∏ j : {j : ι // j ≠ p}, locDim (τ j).1 (τ j).2 := by
      simp [Fintype.card_pi]
    rcases ℓ with ⟨u, v⟩
    cases u <;> cases v
    ·
      have h : (Matrix.kroneckerMap (· * ·) (tensorRepGen (F := F) k
          (fun j : {j : ι // j ≠ p} => τ j) (fun j => e j) (up3 (0 : F) 0 1))
          (locRep (F := F) k (false, false).1 (false, false).2 (e p) (up3 (0 : F) 0 1)) - 1).rank =
          (tensorRepGen (F := F) k (fun j : {j : ι // j ≠ p} => τ j) (fun j => e j)
            (up3 (0 : F) 0 1) - 1).rank :=
        rank_kron_unit k (tensorRepGen (F := F) k (fun j : {j : ι // j ≠ p} => τ j)
          (fun j => e j) (up3 (0 : F) 0 1))
      rw [h]
      have hp : locDim (false, false).1 (false, false).2 *
          ∏ j : {j : ι // j ≠ p}, locDim (τ j).1 (τ j).2 =
          1 * ∏ j : {j : ι // j ≠ p}, locDim (τ j).1 (τ j).2 := rfl
      rw [hp]
      omega
    ·
      have key : Fintype.card (∀ j : {j : ι // j ≠ p}, Fin (locDim (τ j).1 (τ j).2)) +
          (tensorRepGen (F := F) k (fun j : {j : ι // j ≠ p} => τ j) (fun j => e j)
            (up3 (0 : F) 0 1) - 1).rank ≤
          (Matrix.kroneckerMap (· * ·) (tensorRepGen (F := F) k
            (fun j : {j : ι // j ≠ p} => τ j) (fun j => e j) (up3 (0 : F) 0 1))
            (locRep (F := F) k (false, true).1 (false, true).2 (e p) (up3 (0 : F) 0 1)) - 1).rank :=
        rank_kron_free_one (β := Fin 3) (tensorRepGen (F := F) k
          (fun j : {j : ι // j ≠ p} => τ j) (fun j => e j) (up3 (0 : F) 0 1)) _ hRR'
          (dualRep (F := F) k (e p) (up3 (0 : F) 0 1)) 0 1 2 (by decide) (by decide) (by decide)
          (by rw [dualRep_tr0]; rfl) (by rw [dualRep_tr0]; rfl) (by rw [dualRep_tr0]; rfl)
          (by rw [dualRep_tr0]; rfl)
      have hp : locDim (false, true).1 (false, true).2 *
          ∏ j : {j : ι // j ≠ p}, locDim (τ j).1 (τ j).2 =
          3 * ∏ j : {j : ι // j ≠ p}, locDim (τ j).1 (τ j).2 := rfl
      rw [hp]
      omega
    ·
      have key : Fintype.card (∀ j : {j : ι // j ≠ p}, Fin (locDim (τ j).1 (τ j).2)) +
          (tensorRepGen (F := F) k (fun j : {j : ι // j ≠ p} => τ j) (fun j => e j)
            (up3 (0 : F) 0 1) - 1).rank ≤
          (Matrix.kroneckerMap (· * ·) (tensorRepGen (F := F) k
            (fun j : {j : ι // j ≠ p} => τ j) (fun j => e j) (up3 (0 : F) 0 1))
            (locRep (F := F) k (true, false).1 (true, false).2 (e p) (up3 (0 : F) 0 1)) - 1).rank :=
        rank_kron_free_one (β := Fin 3) (tensorRepGen (F := F) k
          (fun j : {j : ι // j ≠ p} => τ j) (fun j => e j) (up3 (0 : F) 0 1)) _ hRR'
          (natRep (F := F) k (e p) (up3 (0 : F) 0 1)) 1 0 2 (by decide) (by decide) (by decide)
          (by rw [natRep_tr0]; rfl) (by rw [natRep_tr0]; rfl) (by rw [natRep_tr0]; rfl)
          (by rw [natRep_tr0]; rfl)
      have hp : locDim (true, false).1 (true, false).2 *
          ∏ j : {j : ι // j ≠ p}, locDim (τ j).1 (τ j).2 =
          3 * ∏ j : {j : ι // j ≠ p}, locDim (τ j).1 (τ j).2 := rfl
      rw [hp]
      omega
    ·
      have key : ({1, 2, 5, 7} : Finset (Fin 8)).card *
          Fintype.card (∀ j : {j : ι // j ≠ p}, Fin (locDim (τ j).1 (τ j).2)) ≤
          (Matrix.kroneckerMap (· * ·) (tensorRepGen (F := F) k
            (fun j : {j : ι // j ≠ p} => τ j) (fun j => e j) (up3 (0 : F) 0 1))
            (locRep (F := F) k (true, true).1 (true, true).2 (e p) (up3 (0 : F) 0 1)) - 1).rank :=
        rank_kron_free (tensorRepGen (F := F) k
          (fun j : {j : ι // j ≠ p} => τ j) (fun j => e j) (up3 (0 : F) 0 1)) _ hRR'
          (adjRep (F := F) k (e p) (up3 (0 : F) 0 1)) ({1, 2, 5, 7} : Finset (Fin 8)) (by
            rw [adjRep_tr0]
            exact adjT0_free k)
      have hp : locDim (true, true).1 (true, true).2 *
          ∏ j : {j : ι // j ≠ p}, locDim (τ j).1 (τ j).2 =
          8 * ∏ j : {j : ι // j ≠ p}, locDim (τ j).1 (τ j).2 := rfl
      rw [hp]
      have e2 : ({1, 2, 5, 7} : Finset (Fin 8)).card = 4 := by decide
      rw [e2] at key
      omega

end Main

section Arrays

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {f : ℕ}

omit [Fintype F] in
theorem dim_le_two_mul_rank_tensorRep (a b : Fin f → Bool) :
    3 ^ cntS a b * 8 ^ cntH a b ≤
      2 * (tensorRep (F := F) F a b (up3 (0 : F) 0 1) - 1).rank + 1 := by
  have h := dim_le_two_mul_rank_add_one (F := F) F (Fintype.card (Fin f)) rfl
    (fun i : Fin f => (a i, b i)) (fun i => (i : ℕ))
  rw [← card_TIdx_eq a b, card_TIdx]
  exact h

theorem rank_tensorRep_involution (a b : Fin f → Bool) {t : SL(3, F)} (ht1 : t ≠ 1)
    (ht2 : t * t = 1) :
    (tensorRep (F := F) F a b t - 1).rank = (tensorRep (F := F) F a b (up3 (0 : F) 0 1) - 1).rank := by
  obtain ⟨g, hg⟩ := exists_conj_transvection t ht1 ht2
  have e1 : tensorRep (F := F) F a b (up3 (0 : F) 0 1) - 1 =
      tensorRep (F := F) F a b g⁻¹ * (tensorRep (F := F) F a b t - 1) *
        tensorRep (F := F) F a b g := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← map_mul, ← map_mul, ← map_mul,
      inv_mul_cancel, map_one, ← hg]
  have hu1 : IsUnit (tensorRep (F := F) F a b g⁻¹).det := by
    refine IsUnit.of_mul_eq_one (tensorRep (F := F) F a b g).det ?_
    rw [← Matrix.det_mul, ← map_mul, inv_mul_cancel, map_one, Matrix.det_one]
  have hu2 : IsUnit (tensorRep (F := F) F a b g).det := by
    refine IsUnit.of_mul_eq_one (tensorRep (F := F) F a b g⁻¹).det ?_
    rw [← Matrix.det_mul, ← map_mul, mul_inv_cancel, map_one, Matrix.det_one]
  rw [e1, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hu2, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hu1]

end Arrays

end CFSG.QuasithinUnique.Setup.X7a
