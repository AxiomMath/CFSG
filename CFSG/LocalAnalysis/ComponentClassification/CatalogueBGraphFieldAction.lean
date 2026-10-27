module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearSemilinearFaithfulness

public section

namespace CFSG.ComponentClassification.CatalogueBGraphField

noncomputable section

open Matrix CatalogueBHigherLinearAction CatalogueBHigherLinearField
open CatalogueBGraphForm CatalogueBLinearSemilinear

universe u

@[expose] def glGraphFieldAut (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    MulAut (GL (Fin n) K) :=
  glFieldAut (Fin n) K sigma * glGraphAut n K

theorem glGraphFieldAut_matrix (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) (g : GL (Fin n) K) :
    (glGraphFieldAut n K sigma g).val =
      (sigma.toRingHom.mapMatrix (g⁻¹).val).transpose := by
  change sigma.toRingHom.mapMatrix (glGraphAut n K g).val = _
  rw [glGraphAut_matrix]
  rfl

@[expose] def slGraphFieldAut (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    MulAut (SpecialLinearGroup (Fin n) K) :=
  slFieldAut (Fin n) K sigma * slGraphAut n K

theorem toGL_slGraphFieldAut (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) (g : SpecialLinearGroup (Fin n) K) :
    SpecialLinearGroup.toGL (slGraphFieldAut n K sigma g) =
      glGraphFieldAut n K sigma (SpecialLinearGroup.toGL g) := by
  change SpecialLinearGroup.toGL (slFieldEquiv (Fin n) sigma (slGraphAut n K g)) = _
  rw [toGL_slFieldEquiv, toGL_slGraphAut]
  rfl

@[expose] def pglGraphFieldAut (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    MulAut (ProjGenLinGroup (Fin n) K) :=
  pglFieldAut (Fin n) K sigma * pglGraphAut n K

theorem pglGraphFieldAut_mk (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) (g : GL (Fin n) K) :
    pglGraphFieldAut n K sigma (ProjGenLinGroup.mk g) =
      ProjGenLinGroup.mk (glGraphFieldAut n K sigma g) := by
  change pglFieldEquiv (Fin n) sigma (pglGraphAut n K (ProjGenLinGroup.mk g)) = _
  rw [pglGraphAut_mk, pglFieldEquiv_mk]
  rfl

@[expose] def pslGraphFieldAut (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    MulAut (ProjectiveSpecialLinearGroup (Fin n) K) :=
  pslFieldAut (Fin n) K sigma * pslGraphAut n K

theorem pslGraphFieldAut_mk (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) (g : SpecialLinearGroup (Fin n) K) :
    pslGraphFieldAut n K sigma (QuotientGroup.mk g) =
      QuotientGroup.mk (slGraphFieldAut n K sigma g) := by
  change pslFieldAut (Fin n) K sigma (pslGraphAut n K (QuotientGroup.mk g)) = _
  rw [pslGraphAut_mk_inverseTranspose, pslFieldAut_mk]
  rfl

theorem toPGL_pslGraphFieldAut (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) (x : ProjectiveSpecialLinearGroup (Fin n) K) :
    ProjectiveSpecialLinearGroup.toPGL (pslGraphFieldAut n K sigma x) =
      pglGraphFieldAut n K sigma (ProjectiveSpecialLinearGroup.toPGL x) := by
  change ProjectiveSpecialLinearGroup.toPGL
    (pslFieldAut (Fin n) K sigma (pslGraphAut n K x)) = _
  rw [toPGL_pslFieldAut, toPGL_pslGraphAut]
  rfl

theorem field_innerDiagonal_commute (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) (A : GL (Fin n) K) :
    pslFieldAut (Fin n) K sigma * innerDiagonalAction n K A =
      innerDiagonalAction n K (glFieldAut (Fin n) K sigma A) *
        pslFieldAut (Fin n) K sigma := by
  have h := semilinearAction_mul n K 1 A sigma 1
  simpa only [semilinearAction, map_one, one_mul, mul_one] using h

theorem graphField_innerDiagonal_commute (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) (A : GL (Fin n) K) :
    pslGraphFieldAut n K sigma * innerDiagonalAction n K A =
      innerDiagonalAction n K (glGraphFieldAut n K sigma A) *
        pslGraphFieldAut n K sigma := by
  unfold pslGraphFieldAut
  rw [mul_assoc, graph_innerDiagonal_commute, ← mul_assoc, field_innerDiagonal_commute,
    mul_assoc]
  rfl

theorem pslGraphFieldAut_mul (n : ℕ) (K : Type u) [Field K]
    (sigma rho : K ≃+* K) :
    pslGraphFieldAut n K sigma * pslGraphFieldAut n K rho =
      pslFieldAut (Fin n) K (sigma * rho) := by
  unfold pslGraphFieldAut
  calc
    _ = pslFieldAut (Fin n) K sigma *
        (pslGraphAut n K * pslFieldAut (Fin n) K rho) * pslGraphAut n K := by group
    _ = pslFieldAut (Fin n) K sigma *
        (pslFieldAut (Fin n) K rho * pslGraphAut n K) * pslGraphAut n K := by
      rw [pslGraphAut_field_commute]
    _ = pslFieldAut (Fin n) K (sigma * rho) := by
      rw [← mul_assoc, mul_assoc (pslFieldAut (Fin n) K sigma *
        pslFieldAut (Fin n) K rho), ← pow_two, pslGraphAut_sq, mul_one, map_mul]

theorem pslGraphFieldAut_sq (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) :
    pslGraphFieldAut n K sigma ^ 2 = pslFieldAut (Fin n) K (sigma ^ 2) := by
  simpa only [pow_two] using pslGraphFieldAut_mul n K sigma sigma

theorem pslGraphFieldAut_sq_eq_one (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) :
    pslGraphFieldAut n K sigma ^ 2 = 1 := by
  rw [pslGraphFieldAut_sq, hsigma, map_one]

theorem pglGraphFieldAut_sq (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) :
    pglGraphFieldAut n K sigma ^ 2 = pglFieldAut (Fin n) K (sigma ^ 2) := by
  unfold pglGraphFieldAut
  calc
    _ = pglFieldAut (Fin n) K sigma *
        (pglGraphAut n K * pglFieldAut (Fin n) K sigma) * pglGraphAut n K := by
      rw [pow_two]
      group
    _ = pglFieldAut (Fin n) K sigma *
        (pglFieldAut (Fin n) K sigma * pglGraphAut n K) * pglGraphAut n K := by
      rw [pglGraphAut_field_commute]
    _ = pglFieldAut (Fin n) K sigma ^ 2 * pglGraphAut n K ^ 2 := by
      rw [pow_two, pow_two]
      group
    _ = pglFieldAut (Fin n) K (sigma ^ 2) := by
      rw [pglGraphAut_sq, mul_one, map_pow]

theorem pglGraphFieldAut_sq_eq_one (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) :
    pglGraphFieldAut n K sigma ^ 2 = 1 := by
  rw [pglGraphFieldAut_sq, hsigma, map_one]

@[expose] def pglGraphFieldAction (n : ℕ) (K : Type u) [Field K]
    (A : GL (Fin n) K) (sigma : K ≃+* K) :
    MulAut (ProjGenLinGroup (Fin n) K) :=
  MulAut.conj (ProjGenLinGroup.mk A) * pglGraphFieldAut n K sigma

theorem pglGraphFieldAction_mk (n : ℕ) (K : Type u) [Field K]
    (A : GL (Fin n) K) (sigma : K ≃+* K) (g : GL (Fin n) K) :
    pglGraphFieldAction n K A sigma (ProjGenLinGroup.mk g) =
      ProjGenLinGroup.mk (A * glGraphFieldAut n K sigma g * A⁻¹) := by
  change MulAut.conj (ProjGenLinGroup.mk A)
    (pglGraphFieldAut n K sigma (ProjGenLinGroup.mk g)) = _
  rw [pglGraphFieldAut_mk, MulAut.conj_apply, map_mul, map_mul, map_inv]

@[expose] def graphFieldAction (n : ℕ) (K : Type u) [Field K]
    (A : GL (Fin n) K) (sigma : K ≃+* K) :
    MulAut (ProjectiveSpecialLinearGroup (Fin n) K) :=
  innerDiagonalAction n K A * pslGraphFieldAut n K sigma

theorem graphFieldAction_mk (n : ℕ) (K : Type u) [Field K]
    (A : GL (Fin n) K) (sigma : K ≃+* K) (g : SpecialLinearGroup (Fin n) K) :
    graphFieldAction n K A sigma (QuotientGroup.mk g) =
      QuotientGroup.mk (slConjugation n K A (slGraphFieldAut n K sigma g)) := by
  change innerDiagonalAction n K A (pslGraphFieldAut n K sigma (QuotientGroup.mk g)) = _
  rw [pslGraphFieldAut_mk]
  exact innerDiagonalAction_mk n K A _

theorem toPGL_graphFieldAction (n : ℕ) (K : Type u) [Field K]
    (A : GL (Fin n) K) (sigma : K ≃+* K)
    (x : ProjectiveSpecialLinearGroup (Fin n) K) :
    ProjectiveSpecialLinearGroup.toPGL (graphFieldAction n K A sigma x) =
      pglGraphFieldAction n K A sigma (ProjectiveSpecialLinearGroup.toPGL x) := by
  change ProjectiveSpecialLinearGroup.toPGL
    (innerDiagonalAction n K A (pslGraphFieldAut n K sigma x)) = _
  rw [innerDiagonalAction_eq_pglAction, toPGL_pglAction, toPGL_pslGraphFieldAut]
  rfl

theorem graphFieldAction_eq_semilinear_graph (n : ℕ) (K : Type u) [Field K]
    (A : GL (Fin n) K) (sigma : K ≃+* K) :
    graphFieldAction n K A sigma = semilinearAction n K A sigma * pslGraphAut n K := by
  simp only [graphFieldAction, pslGraphFieldAut, semilinearAction, mul_assoc]

theorem graphFieldAction_mul (n : ℕ) (K : Type u) [Field K]
    (A B : GL (Fin n) K) (sigma rho : K ≃+* K) :
    graphFieldAction n K A sigma * graphFieldAction n K B rho =
      semilinearAction n K (A * glGraphFieldAut n K sigma B) (sigma * rho) := by
  unfold graphFieldAction
  calc
    _ = innerDiagonalAction n K A *
        (pslGraphFieldAut n K sigma * innerDiagonalAction n K B) *
        pslGraphFieldAut n K rho := by group
    _ = innerDiagonalAction n K A *
        (innerDiagonalAction n K (glGraphFieldAut n K sigma B) *
          pslGraphFieldAut n K sigma) * pslGraphFieldAut n K rho := by
      rw [graphField_innerDiagonal_commute]
    _ = semilinearAction n K (A * glGraphFieldAut n K sigma B) (sigma * rho) := by
      rw [← mul_assoc, mul_assoc (innerDiagonalAction n K A *
        innerDiagonalAction n K (glGraphFieldAut n K sigma B)), pslGraphFieldAut_mul]
      rw [← map_mul]
      rfl

theorem graphFieldAction_sq (n : ℕ) (K : Type u) [Field K]
    (A : GL (Fin n) K) (sigma : K ≃+* K) :
    graphFieldAction n K A sigma ^ 2 =
      semilinearAction n K (A * glGraphFieldAut n K sigma A) (sigma ^ 2) := by
  simpa only [pow_two] using graphFieldAction_mul n K A A sigma sigma

theorem graphField_involution_scalar (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 3 ≤ n) (A : GL (Fin n) K) (sigma : K ≃+* K)
    (hsquare : graphFieldAction n K A sigma ^ 2 = 1) :
    sigma ^ 2 = 1 ∧ ∃ c : Kˣ,
      GeneralLinearGroup.scalar (Fin n) c = A * glGraphFieldAut n K sigma A := by
  rw [graphFieldAction_sq] at hsquare
  exact (semilinearAction_eq_one_iff n K (by omega) (Or.inl hn) _ _).mp hsquare

theorem inner_graphField_conjugation (n : ℕ) (K : Type u) [Field K]
    (H : GL (Fin n) K) (sigma : K ≃+* K) :
    innerDiagonalAction n K H * pslGraphFieldAut n K sigma *
        (innerDiagonalAction n K H)⁻¹ =
      graphFieldAction n K (H * glGraphFieldAut n K sigma H⁻¹) sigma := by
  rw [← map_inv, mul_assoc, graphField_innerDiagonal_commute, ← mul_assoc, ← map_mul]
  rfl

theorem graphFieldAction_scalar_mul (n : ℕ) (K : Type u) [Field K]
    (c : Kˣ) (A : GL (Fin n) K) (sigma : K ≃+* K) :
    graphFieldAction n K (GeneralLinearGroup.scalar (Fin n) c * A) sigma =
      graphFieldAction n K A sigma := by
  rw [graphFieldAction, map_mul, innerDiagonalAction_scalar, one_mul]
  rfl

end

end CFSG.ComponentClassification.CatalogueBGraphField
