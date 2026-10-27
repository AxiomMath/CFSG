module

public import CFSG.CharacterTheory.FrobeniusDeterminant.Defs
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG

namespace FrobeniusDeterminant.Norm

open scoped BigOperators
open Matrix

theorem det_blockDiagonal_const {R : Type*} [CommRing R] (n : ℕ)
    (a : Matrix (Fin n) (Fin n) R) :
    (Matrix.blockDiagonal (fun _ : Fin n => a)).det = a.det ^ n := by
  rw [Matrix.det_blockDiagonal]
  exact Fin.prod_const n a.det

theorem norm_prod {R S T : Type*} [CommRing R]
    [Ring S] [Algebra R S] [Module.Free R S] [Module.Finite R S]
    [Ring T] [Algebra R T] [Module.Free R T] [Module.Finite R T]
    (x : S) (y : T) :
    Algebra.norm R (x, y) = Algebra.norm R x * Algebra.norm R y := by
  rw [Algebra.norm_apply, Algebra.norm_apply, Algebra.norm_apply]
  have h : (Algebra.lmul R (S × T)) (x, y) =
      LinearMap.prodMap ((Algebra.lmul R S) x) ((Algebra.lmul R T) y) := by
    ext z <;> rfl
  rw [h, LinearMap.det_prodMap]

noncomputable def finConsAlgEquiv (R : Type*) [CommRing R] {n : ℕ}
    (A : Fin (n + 1) → Type*) [∀ i, Ring (A i)] [∀ i, Algebra R (A i)] :
    (∀ i, A i) ≃ₐ[R] A 0 × (∀ i : Fin n, A i.succ) where
  toFun x := (x 0, fun i => x i.succ)
  invFun x := Fin.cons x.1 x.2
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  right_inv x := by
    apply Prod.ext
    · rfl
    · funext i
      rfl
  map_mul' x y := rfl
  map_add' x y := rfl
  commutes' r := rfl

theorem norm_pi_fin {R : Type*} [CommRing R] :
    ∀ (n : ℕ) (A : Fin n → Type*) [∀ i, Ring (A i)] [∀ i, Algebra R (A i)]
      [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)]
      (x : ∀ i, A i), Algebra.norm R x = ∏ i, Algebra.norm R (x i)
  | 0, A, _, _, _, _, x => by
      have : Subsingleton (∀ i : Fin 0, A i) :=
        ⟨fun a b => funext fun i => Fin.elim0 i⟩
      rw [Algebra.norm_apply]
      simpa using LinearMap.det_eq_one_of_subsingleton ((Algebra.lmul R _) x)
  | n + 1, A, _, _, _, _, x => by
      rw [← Algebra.norm_eq_of_algEquiv (finConsAlgEquiv R A) x]
      rw [norm_prod]
      rw [norm_pi_fin n (fun i => A i.succ)]
      change Algebra.norm R (x 0) *
        (∏ i : Fin n, Algebra.norm R (x i.succ)) = _
      rw [Fin.prod_univ_succ]

theorem norm_matrix_complex (n : ℕ) (a : Matrix (Fin n) (Fin n) ℂ) :
    Algebra.norm ℂ a = a.det ^ n := by
  rw [Algebra.norm_eq_matrix_det (Matrix.stdBasis ℂ (Fin n) (Fin n))]
  have h : Algebra.leftMulMatrix (Matrix.stdBasis ℂ (Fin n) (Fin n)) a =
      Matrix.blockDiagonal (fun _ : Fin n => a) := by
    ext ⟨i, k⟩ ⟨j, l⟩
    rw [Algebra.leftMulMatrix_eq_repr_mul, Matrix.stdBasis_eq_single]
    change (a * (Matrix.single j l 1 : Matrix (Fin n) (Fin n) ℂ)) i k = _
    by_cases hkl : k = l
    · subst l
      simp [Matrix.mul_apply, Matrix.single_apply]
    · rw [Matrix.blockDiagonal_apply_ne (fun _ : Fin n => a) i j hkl]
      simp [Matrix.mul_apply, Ne.symm hkl]
  rw [h, det_blockDiagonal_const]

end FrobeniusDeterminant.Norm

end CFSG
