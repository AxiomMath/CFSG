module

public import CFSG.LinearAlgebra.FiniteTriangularDiagonalization
public import CFSG.LinearAlgebra.UpperTriangularNilpotent

public section

namespace CFSG.LinearAlgebra

open Matrix
open scoped BigOperators

universe u v w

theorem centralizer_nilpotent_of_finite_triangular_detector
    {k : Type u} [Field k]
    {E : Type v} [Group E]
    {A : Type w} [CommGroup A]
    {n : ℕ}
    (rho : E →* TauCeti.upperTriangularGroup (Fin n) k)
    (hrho : Function.Injective rho)
    (pi : E →* A)
    (delta : A →* (Fin n → kˣ))
    (heq : ∀ e : E, TauCeti.UpperTriangularGroup.diag (rho e) = delta (pi e))
    (F : Subgroup A) [Finite F]
    (hcard : (Nat.card F : k) ≠ 0)
    (s : F →* E)
    (hs : ∀ f : F, pi (s f) = (f : A))
    (hdet : ∀ M : Matrix (Fin n) (Fin n) k,
      (∀ f : F,
        Matrix.diagonal (fun i => ((delta (f : A) i : kˣ) : k)) * M =
          M * Matrix.diagonal (fun i => ((delta (f : A) i : kˣ) : k))) →
      ∀ a : A,
        Matrix.diagonal (fun i => ((delta a i : kˣ) : k)) * M =
          M * Matrix.diagonal (fun i => ((delta a i : kˣ) : k))) :
    Group.IsNilpotent (Subgroup.centralizer (s.range : Set E)) := by
  classical
  let diagMat : A → Matrix (Fin n) (Fin n) k := fun a =>
    Matrix.diagonal (fun i => ((delta a i : kˣ) : k))
  obtain ⟨A0, hA0, hA0eq⟩ :=
    exists_upperUnitriangular_diagonalizing_matrix (k := k) (F := F) hcard (rho.comp s)
  have hA0eq' : ∀ f : F,
      ((((rho.comp s) f : TauCeti.upperTriangularGroup (Fin n) k) : GL (Fin n) k) :
          Matrix (Fin n) (Fin n) k) * A0 = A0 * diagMat (f : A) := by
    intro f
    have hd : TauCeti.UpperTriangularGroup.diag
        ((rho.comp s) f) = delta (f : A) := by
      rw [show (rho.comp s) f = rho (s f) from rfl, heq, hs]
    simpa only [diagMat, hd] using hA0eq f
  let a : TauCeti.upperTriangularGroup (Fin n) k :=
    ⟨hA0.toGL, by simpa using hA0.isUpperTriangular⟩
  have ha_apply : (a : GL (Fin n) k) = hA0.toGL := rfl
  have ha_mat : (((a : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) = A0 := by
    rw [ha_apply, hA0.coe_toGL]
  have hdiag_a : TauCeti.UpperTriangularGroup.diag a = 1 := by
    rw [TauCeti.UpperTriangularGroup.diag_eq_one_iff,
      TauCeti.UpperUnitriangularGroup.mem_iff]
    simpa only [ha_mat] using hA0
  let rho' : E →* TauCeti.upperTriangularGroup (Fin n) k :=
    (MulAut.conj a⁻¹).toMonoidHom.comp rho
  have hrho'_apply : ∀ e : E, rho' e = a⁻¹ * rho e * a := by
    intro e
    simp only [rho', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv]
  have hrho'_inj : Function.Injective rho' := by
    intro x y hxy
    exact hrho ((MulAut.conj a⁻¹).injective hxy)
  have hdiag_rho' : ∀ e : E,
      TauCeti.UpperTriangularGroup.diag (rho' e) =
        TauCeti.UpperTriangularGroup.diag (rho e) := by
    intro e
    simp only [hrho'_apply, map_mul, map_inv, hdiag_a, inv_one, one_mul, mul_one]
  have hdiag_eq : ∀ e : E,
      TauCeti.UpperTriangularGroup.diag (rho' e) = delta (pi e) := by
    intro e
    rw [hdiag_rho' e, heq e]
  have hrho'_s : ∀ f : F,
      rho' (s f) = TauCeti.UpperTriangularGroup.diagonalHom (delta (f : A)) := by
    intro f
    have hGL : ((rho (s f) : TauCeti.upperTriangularGroup (Fin n) k) : GL (Fin n) k) *
        (a : GL (Fin n) k) =
        (a : GL (Fin n) k) * TauCeti.diagGL (delta (f : A)) := by
      apply Units.ext
      simpa only [MonoidHom.comp_apply, ha_mat, diagMat, TauCeti.diagGL_coe,
        Units.val_mul] using hA0eq' f
    have hUT : rho (s f) * a =
        a * TauCeti.UpperTriangularGroup.diagonalHom (delta (f : A)) := by
      apply Subtype.ext
      simpa only [Subgroup.coe_mul, TauCeti.UpperTriangularGroup.coe_diagonalHom]
        using hGL
    calc
      rho' (s f) = a⁻¹ * rho (s f) * a := hrho'_apply (s f)
      _ = a⁻¹ * (rho (s f) * a) := by group
      _ = a⁻¹ * (a * TauCeti.UpperTriangularGroup.diagonalHom (delta (f : A))) := by
            rw [hUT]
      _ = TauCeti.UpperTriangularGroup.diagonalHom (delta (f : A)) := by group
  let C : Subgroup E := Subgroup.centralizer (s.range : Set E)
  let N : Subgroup (TauCeti.upperTriangularGroup (Fin n) k) := C.map rho'
  have hN : Group.IsNilpotent N := by
    apply upperTriangularSubgroup_nilpotent_of_diagonal_commute (N := N)
    intro x y
    obtain ⟨x0, hx0C, hx0eq⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨y0, hy0C, hy0eq⟩ := Subgroup.mem_map.mp y.2
    have hx : (x : TauCeti.upperTriangularGroup (Fin n) k) = rho' x0 := hx0eq.symm
    have hy : (y : TauCeti.upperTriangularGroup (Fin n) k) = rho' y0 := hy0eq.symm
    have hcommF : ∀ f : F,
        diagMat (f : A) *
            ((((rho' y0 : TauCeti.upperTriangularGroup (Fin n) k) : GL (Fin n) k) :
              Matrix (Fin n) (Fin n) k)) =
          ((((rho' y0 : TauCeti.upperTriangularGroup (Fin n) k) : GL (Fin n) k) :
              Matrix (Fin n) (Fin n) k)) * diagMat (f : A) := by
      intro f
      have hsf_mem : s f ∈ s.range := ⟨f, rfl⟩
      have hcommE : (s f) * y0 = y0 * (s f) :=
        (Subgroup.mem_centralizer_iff.mp hy0C) (s f) hsf_mem
      have hcommUT : rho' (s f) * rho' y0 = rho' y0 * rho' (s f) := by
        rw [← map_mul, ← map_mul, hcommE]
      have hcommMat :
          ((((rho' (s f) : TauCeti.upperTriangularGroup (Fin n) k) : GL (Fin n) k) :
              Matrix (Fin n) (Fin n) k)) *
            ((((rho' y0 : TauCeti.upperTriangularGroup (Fin n) k) : GL (Fin n) k) :
              Matrix (Fin n) (Fin n) k)) =
          ((((rho' y0 : TauCeti.upperTriangularGroup (Fin n) k) : GL (Fin n) k) :
              Matrix (Fin n) (Fin n) k)) *
            ((((rho' (s f) : TauCeti.upperTriangularGroup (Fin n) k) : GL (Fin n) k) :
              Matrix (Fin n) (Fin n) k)) := by
        simpa only [Subgroup.coe_mul, Units.val_mul] using
          congrArg (fun z : TauCeti.upperTriangularGroup (Fin n) k =>
            (((z : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) hcommUT
      have hdiagMat_eq : diagMat (f : A) =
          ((((rho' (s f) : TauCeti.upperTriangularGroup (Fin n) k) : GL (Fin n) k) :
            Matrix (Fin n) (Fin n) k)) := by
        simp only [diagMat, hrho'_s f, TauCeti.UpperTriangularGroup.coe_diagonalHom,
          TauCeti.diagGL_coe]
      calc
        diagMat (f : A) *
            ((((rho' y0 : TauCeti.upperTriangularGroup (Fin n) k) : GL (Fin n) k) :
              Matrix (Fin n) (Fin n) k)) =
            ((((rho' (s f) : TauCeti.upperTriangularGroup (Fin n) k) : GL (Fin n) k) :
              Matrix (Fin n) (Fin n) k)) *
              ((((rho' y0 : TauCeti.upperTriangularGroup (Fin n) k) : GL (Fin n) k) :
                Matrix (Fin n) (Fin n) k)) := by rw [hdiagMat_eq]
        _ = ((((rho' y0 : TauCeti.upperTriangularGroup (Fin n) k) : GL (Fin n) k) :
              Matrix (Fin n) (Fin n) k)) *
              ((((rho' (s f) : TauCeti.upperTriangularGroup (Fin n) k) : GL (Fin n) k) :
                Matrix (Fin n) (Fin n) k)) := hcommMat
        _ = ((((rho' y0 : TauCeti.upperTriangularGroup (Fin n) k) : GL (Fin n) k) :
              Matrix (Fin n) (Fin n) k)) * diagMat (f : A) := by rw [hdiagMat_eq]
    have hcommPi := hdet _ hcommF (pi x0)
    rw [hx, hy]
    simpa only [diagMat, hdiag_eq x0] using hcommPi
  let eC : C ≃* N := Subgroup.equivMapOfInjective C rho' hrho'_inj
  exact (Group.isNilpotent_congr eC).mpr hN

end CFSG.LinearAlgebra
