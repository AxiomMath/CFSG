module

public import Mathlib.LinearAlgebra.Matrix.Permutation

public section

namespace CFSG.GroupTheory

theorem exists_nontrivial_repr_card (K : Type) [Group K] [Finite K] [Nontrivial K] :
    ∃ n : ℕ, ∃ f : K →* Matrix.GeneralLinearGroup (Fin n) (ZMod 2), f ≠ 1 := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  let n : ℕ := Fintype.card K
  let e : K ≃ Fin n := Fintype.equivFin K
  let ρ : K →* Equiv.Perm K := MulAction.toPermHom K K
  let τ : K →* Equiv.Perm (Fin n) :=
    { toFun := fun g => Equiv.trans e.symm (Equiv.trans (ρ g) e)
      map_one' := by ext i; simp [ρ]
      map_mul' := by
        intro a b
        ext i
        simp only [Equiv.trans_apply, Equiv.Perm.coe_mul, Function.comp_apply, map_mul]
        simp [mul_smul] }
  let f : K →* Matrix.GeneralLinearGroup (Fin n) (ZMod 2) :=
    (Matrix.permMatrixHom (n := Fin n) (R := ZMod 2)).toHomUnits.comp τ
  refine ⟨n, f, ?_⟩
  intro hf
  obtain ⟨g, hg⟩ := exists_ne (1 : K)
  have hmat : ((f g : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
    have hfg : f g = 1 := by simpa [hf]
    rw [hfg]
    rfl
  have hmat' : (Matrix.permMatrixHom (n := Fin n) (R := ZMod 2) (τ g) :
      Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
    simpa [f, MonoidHom.coe_toHomUnits] using hmat
  have hτ1 : τ g (e 1) = e g := by
    simp [τ, ρ]
  have hne : e (1 : K) ≠ e g := fun h => hg (e.injective h).symm
  have hne' : τ g (e 1) ≠ e 1 := fun h => hne (hτ1.symm.trans h).symm
  have hentry := congrArg (fun M : Matrix (Fin n) (Fin n) (ZMod 2) =>
    M (τ g (e 1)) (e 1)) hmat'
  have hzero : (1 : Matrix (Fin n) (Fin n) (ZMod 2)) (τ g (e 1)) (e 1) = 0 := by
    rw [Matrix.one_apply_ne hne']
  have hone : (Matrix.permMatrixHom (n := Fin n) (R := ZMod 2) (τ g) :
      Matrix (Fin n) (Fin n) (ZMod 2)) (τ g (e 1)) (e 1) = 1 := by
    rw [Matrix.permMatrixHom_apply]
    simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      Option.mem_def, Option.some.injEq]
    simp
  rw [hone, hzero] at hentry
  exact absurd hentry (by decide)

end CFSG.GroupTheory
