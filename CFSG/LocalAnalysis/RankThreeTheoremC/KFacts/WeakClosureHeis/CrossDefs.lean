module

public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.Algebra.Group.Pi.Units

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open Matrix

variable {L : Type} [Field L]

@[expose] noncomputable def diagGL (n : ℕ) : (Fin n → Lˣ) →* GL (Fin n) L :=
  (Units.map (Matrix.diagonalRingHom (Fin n) L).toMonoidHom).comp
    (MulEquiv.piUnits (M := fun _ : Fin n => L)).symm.toMonoidHom

theorem coe_diagGL (n : ℕ) (u : Fin n → Lˣ) :
    ((diagGL n u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal fun i => (u i : L) :=
  rfl

theorem det_diagGL (n : ℕ) (u : Fin n → Lˣ) :
    ((diagGL n u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).det = ∏ i, (u i : L) := by
  rw [coe_diagGL, Matrix.det_diagonal]

@[expose] noncomputable def permGL (n : ℕ) : Equiv.Perm (Fin n) →* GL (Fin n) L :=
  (Matrix.permMatrixHom (n := Fin n) (R := L)).toHomUnits

theorem coe_permGL (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    ((permGL n σ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = (σ⁻¹).permMatrix L :=
  rfl

theorem det_permGL (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    ((permGL n σ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).det = ((Equiv.Perm.sign σ : ℤˣ) : ℤ) := by
  rw [coe_permGL, Matrix.det_permutation]
  simp

theorem permGL_mul_diagGL_mul_inv (n : ℕ) (σ : Equiv.Perm (Fin n)) (u : Fin n → Lˣ) :
    permGL n σ * diagGL n u * (permGL n σ)⁻¹ = diagGL n (fun i => u (σ⁻¹ i)) := by
  rw [← map_inv]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_permGL, coe_permGL, coe_diagGL, coe_diagGL]
  ext i j
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, inv_inv]
  by_cases hij : i = j
  · subst hij
    rw [Finset.sum_eq_single (σ.symm i)]
    · simp
    · intro b _ hb
      by_cases h : σ b = i
      · exact absurd ((Equiv.symm_apply_eq σ).2 h.symm |>.symm) hb
      · simp [h]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · simp only [hij, if_false]
    apply Finset.sum_eq_zero
    intro b _
    by_cases h1 : σ b = i
    · by_cases h2 : σ.symm i = b
      · simp [h1, h2, hij]
      · simp [h2]
    · have h2 : ¬ σ.symm i = b := fun h => h1 (by rw [← h]; simp)
      simp [h2]

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
