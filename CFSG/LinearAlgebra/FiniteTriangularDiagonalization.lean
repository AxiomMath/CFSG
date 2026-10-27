module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Basic

public section

namespace CFSG.LinearAlgebra

open Matrix
open scoped BigOperators

universe u v

theorem exists_upperUnitriangular_diagonalizing_matrix
    {k : Type u} [Field k]
    {F : Type v} [Group F] [Finite F]
    (hm : (Nat.card F : k) ≠ 0)
    {n : ℕ}
    (rho : F →* TauCeti.upperTriangularGroup (Fin n) k) :
    ∃ A : Matrix (Fin n) (Fin n) k,
      A.IsUpperUnitriangular ∧
      ∀ f : F,
        ((rho f : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * A =
          A * Matrix.diagonal
            (fun i => ((TauCeti.UpperTriangularGroup.diag (rho f) i : kˣ) : k)) := by
  classical
  let fintypeF : Fintype F := Fintype.ofFinite F
  let lam : F → Fin n → kˣ := fun f i => TauCeti.UpperTriangularGroup.diag (rho f) i
  let rhoM : F → Matrix (Fin n) (Fin n) k :=
    fun f => ((rho f : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
  let A : Matrix (Fin n) (Fin n) k :=
    fun j i => ((Nat.card F : k)⁻¹) *
      ∑ f : F, (((lam f i)⁻¹ : kˣ) : k) * rhoM f j i
  have hrhoM_mul : ∀ f g : F, rhoM (f * g) = rhoM f * rhoM g := by
    intro f g
    dsimp only [rhoM]
    rw [map_mul]
    rfl
  have hlam_mul : ∀ f g : F, lam (f * g) = lam f * lam g := by
    intro f g
    funext i
    dsimp only [lam]
    rw [map_mul]
    simp
  have hAupper : A.IsUpperTriangular := by
    intro j i hji
    dsimp only [A]
    rw [Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro f _
    dsimp only [rhoM]
    rw [TauCeti.UpperTriangularGroup.isUpperTriangular (rho f) hji]
    simp
  have hAdiag : ∀ i : Fin n, A i i = 1 := by
    intro i
    dsimp only [A]
    have hterm : ∀ f : F,
        (((lam f i)⁻¹ : kˣ) : k) * rhoM f i i = 1 := by
      intro f
      dsimp only [rhoM]
      rw [← TauCeti.UpperTriangularGroup.diag_apply_val (rho f) i]
      simp only [lam, Units.val_inv_eq_inv_val]
      exact inv_mul_cancel₀ (Units.ne_zero (lam f i))
    calc
      ((Nat.card F : k)⁻¹) * ∑ f : F,
          (((lam f i)⁻¹ : kˣ) : k) * rhoM f i i =
          ((Nat.card F : k)⁻¹) * ∑ _f : F, (1 : k) := by
            congr 1
            apply Finset.sum_congr rfl
            intro f _
            exact hterm f
      _ = ((Nat.card F : k)⁻¹) * (Nat.card F : k) := by
            rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
            simp
      _ = 1 := inv_mul_cancel₀ hm
  have hAction : ∀ g : F,
      rhoM g * A = A * Matrix.diagonal
        (fun i => ((lam g i : kˣ) : k)) := by
    intro g
    ext j i
    have hLHS :
        (rhoM g * A) j i =
          ((Nat.card F : k)⁻¹) *
            ∑ f : F, (((lam f i)⁻¹ : kˣ) : k) * rhoM (g * f) j i := by
      rw [Matrix.mul_apply]
      dsimp only [A]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro f _
      calc
        (∑ x : Fin n,
            rhoM g j x * (((Nat.card F : k)⁻¹) *
              ((((lam f i)⁻¹ : kˣ) : k) * rhoM f x i))) =
            (((Nat.card F : k)⁻¹) * (((lam f i)⁻¹ : kˣ) : k)) *
              ∑ x : Fin n, rhoM g j x * rhoM f x i := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro x _
                ring
        _ = ((Nat.card F : k)⁻¹) *
              ((((lam f i)⁻¹ : kˣ) : k) *
                ∑ x : Fin n, rhoM g j x * rhoM f x i) := by ring
        _ = ((Nat.card F : k)⁻¹) *
              ((((lam f i)⁻¹ : kˣ) : k) * (rhoM g * rhoM f) j i) := by
                rw [← Matrix.mul_apply]
        _ = ((Nat.card F : k)⁻¹) *
              ((((lam f i)⁻¹ : kˣ) : k) * rhoM (g * f) j i) := by
                rw [← hrhoM_mul]
    have hsum :
        (∑ f : F, (((lam f i)⁻¹ : kˣ) : k) * rhoM (g * f) j i) =
          (∑ f : F, (((lam f i)⁻¹ : kˣ) : k) * rhoM f j i) *
            ((lam g i : kˣ) : k) := by
      calc
        (∑ f : F, (((lam f i)⁻¹ : kˣ) : k) * rhoM (g * f) j i) =
            ∑ f : F, (((lam f i)⁻¹ : kˣ) : k) * ((lam g i : kˣ) : k) *
              rhoM f j i := by
              refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ ?_
              intro f
              dsimp only [Equiv.coe_mulLeft]
              have hcoef : ((lam (g * f) i)⁻¹ : kˣ) * lam g i = (lam f i)⁻¹ := by
                rw [hlam_mul]
                change ((lam g i) * (lam f i))⁻¹ * lam g i = (lam f i)⁻¹
                group
              rw [← Units.val_mul, hcoef]
        _ = (∑ f : F, (((lam f i)⁻¹ : kˣ) : k) * rhoM f j i) *
              ((lam g i : kˣ) : k) := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro f _
              ring
    calc
      (rhoM g * A) j i =
          ((Nat.card F : k)⁻¹) *
            ∑ f : F, (((lam f i)⁻¹ : kˣ) : k) * rhoM (g * f) j i := hLHS
      _ = ((Nat.card F : k)⁻¹) *
            ((∑ f : F, (((lam f i)⁻¹ : kˣ) : k) * rhoM f j i) *
              ((lam g i : kˣ) : k)) := by rw [hsum]
      _ = (((Nat.card F : k)⁻¹) *
            ∑ f : F, (((lam f i)⁻¹ : kˣ) : k) * rhoM f j i) *
              ((lam g i : kˣ) : k) := by ring
      _ = (A * Matrix.diagonal (fun i => ((lam g i : kˣ) : k))) j i := by
            rw [Matrix.mul_diagonal]
  refine ⟨A, ?_, hAction⟩
  exact (Matrix.isUpperUnitriangular_def A).mpr ⟨hAupper, hAdiag⟩


end CFSG.LinearAlgebra
