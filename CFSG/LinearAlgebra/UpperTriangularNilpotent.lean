module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Nilpotent
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.LinearAlgebra

open Matrix
open scoped BigOperators

universe u

theorem upperTriangularSubgroup_nilpotent_of_diagonal_commute
    {k : Type u} [Field k] {n : ℕ}
    {N : Subgroup (TauCeti.upperTriangularGroup (Fin n) k)}
    (hcen : ∀ x y : N,
      Matrix.diagonal
          (fun i => (((TauCeti.UpperTriangularGroup.diag
            (x : TauCeti.upperTriangularGroup (Fin n) k)) i : kˣ) : k)) *
        (((y : TauCeti.upperTriangularGroup (Fin n) k) : GL (Fin n) k) :
          Matrix (Fin n) (Fin n) k) =
      (((y : TauCeti.upperTriangularGroup (Fin n) k) : GL (Fin n) k) :
          Matrix (Fin n) (Fin n) k) *
        Matrix.diagonal
          (fun i => (((TauCeti.UpperTriangularGroup.diag
            (x : TauCeti.upperTriangularGroup (Fin n) k)) i : kˣ) : k))) :
    Group.IsNilpotent N := by
  classical
  let D : N → TauCeti.upperTriangularGroup (Fin n) k := fun x =>
    TauCeti.UpperTriangularGroup.diagonalHom
      (TauCeti.UpperTriangularGroup.diag
        (x : TauCeti.upperTriangularGroup (Fin n) k))
  have hD_mul : ∀ x y : N, D (x * y) = D x * D y := by
    intro x y
    simp only [D, Subgroup.coe_mul, map_mul]
  have hD_comm : ∀ x y : N, Commute (D x) (D y) := by
    intro x y
    apply Subtype.ext
    apply Units.ext
    simp only [D, Subgroup.coe_mul, Units.val_mul,
      TauCeti.UpperTriangularGroup.coe_diagonalHom, TauCeti.diagGL_coe]
    exact Matrix.commute_diagonal _ _
  have hcen' : ∀ x y : N,
      Commute (D x) (y : TauCeti.upperTriangularGroup (Fin n) k) := by
    intro x y
    apply Subtype.ext
    apply Units.ext
    dsimp only [D]
    simp only [Subgroup.coe_mul, Units.val_mul,
      TauCeti.UpperTriangularGroup.coe_diagonalHom, TauCeti.diagGL_coe]
    simpa only [Units.val_mul, Subgroup.coe_mul, TauCeti.diagGL_coe] using hcen x y
  let u : N → TauCeti.upperUnitriangularGroup (Fin n) k := fun x =>
    ⟨(((D x)⁻¹ * (x : TauCeti.upperTriangularGroup (Fin n) k) :
        TauCeti.upperTriangularGroup (Fin n) k) : GL (Fin n) k), by
      exact (TauCeti.UpperTriangularGroup.diag_eq_one_iff
        (g := (D x)⁻¹ * (x : TauCeti.upperTriangularGroup (Fin n) k))).mp (by
          rw [map_mul, map_inv, TauCeti.UpperTriangularGroup.diag_diagonalHom]
          simp)⟩
  have hu_one : u 1 = 1 := by
    have hφ : ((D 1)⁻¹ * (1 : TauCeti.upperTriangularGroup (Fin n) k) :
        TauCeti.upperTriangularGroup (Fin n) k) = 1 := by
      dsimp only [D]
      simp
    apply Subtype.ext
    exact congrArg (fun z : TauCeti.upperTriangularGroup (Fin n) k =>
      (z : GL (Fin n) k)) hφ
  have hu_mul : ∀ x y : N, u (x * y) = u x * u y := by
    intro x y
    have hφ : ((D (x * y))⁻¹ * ((x * y : N) :
        TauCeti.upperTriangularGroup (Fin n) k) :
          TauCeti.upperTriangularGroup (Fin n) k) =
        ((D x)⁻¹ * (x : TauCeti.upperTriangularGroup (Fin n) k)) *
          ((D y)⁻¹ * (y : TauCeti.upperTriangularGroup (Fin n) k)) := by
      rw [show (x * y : N) = (x : TauCeti.upperTriangularGroup (Fin n) k) *
          (y : TauCeti.upperTriangularGroup (Fin n) k) by
            exact Subgroup.coe_mul (H := N) x y]
      rw [show D (x * y) = D y * D x by
        rw [hD_mul]
        exact hD_comm x y]
      rw [_root_.mul_inv_rev]
      have hDy : (D y)⁻¹ * (x : TauCeti.upperTriangularGroup (Fin n) k) =
          (x : TauCeti.upperTriangularGroup (Fin n) k) * (D y)⁻¹ := by
        exact (hcen' y x).inv_left.eq
      rw [show (D x)⁻¹ * (D y)⁻¹ *
            ((x : TauCeti.upperTriangularGroup (Fin n) k) *
              (y : TauCeti.upperTriangularGroup (Fin n) k)) =
          (D x)⁻¹ * ((D y)⁻¹ *
            (x : TauCeti.upperTriangularGroup (Fin n) k)) *
              (y : TauCeti.upperTriangularGroup (Fin n) k) by group]
      rw [hDy]
      group
    apply Subtype.ext
    exact congrArg (fun z : TauCeti.upperTriangularGroup (Fin n) k =>
      (z : GL (Fin n) k)) hφ
  let φ : N →* TauCeti.upperUnitriangularGroup (Fin n) k :=
    MonoidHom.mk' u hu_mul
  have hφ_apply : ∀ x : N, φ x = u x := fun x => rfl
  have hker : φ.ker ≤ Subgroup.center N := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : u x = 1 := by simpa only [hφ_apply] using hx
    have hxUT : ((D x)⁻¹ * (x : TauCeti.upperTriangularGroup (Fin n) k) :
        TauCeti.upperTriangularGroup (Fin n) k) = 1 := by
      apply Subtype.ext
      have hxgl : (u x : GL (Fin n) k) = 1 :=
        congrArg (fun z : TauCeti.upperUnitriangularGroup (Fin n) k =>
          (z : GL (Fin n) k)) hx'
      have huval : (u x : GL (Fin n) k) =
          (((D x)⁻¹ * (x : TauCeti.upperTriangularGroup (Fin n) k) :
            TauCeti.upperTriangularGroup (Fin n) k) : GL (Fin n) k) := rfl
      rwa [huval] at hxgl
    have hxD : (x : TauCeti.upperTriangularGroup (Fin n) k) = D x := by
      calc
        (x : TauCeti.upperTriangularGroup (Fin n) k) =
            D x * ((D x)⁻¹ * (x : TauCeti.upperTriangularGroup (Fin n) k)) := by group
        _ = D x * 1 := by rw [hxUT]
        _ = D x := by simp
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hxD]
    exact (hcen' x y).symm
  exact Subgroup.isNilpotent_of_ker_le_center φ hker

end CFSG.LinearAlgebra
