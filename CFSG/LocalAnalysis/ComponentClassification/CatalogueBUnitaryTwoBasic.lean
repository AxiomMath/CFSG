module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianMatrix
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBUnitaryTwo

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

universe u v

variable {E : Type u} [Field E]

@[expose] def hyperbolicMatrix : Matrix (Fin 2) (Fin 2) E := !![0, 1; 1, 0]

@[expose] def hyperbolicGL : GL (Fin 2) E where
  val := hyperbolicMatrix
  inv := hyperbolicMatrix
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hyperbolicMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hyperbolicMatrix, Matrix.mul_apply, Fin.sum_univ_two]

variable (sigma : E ≃+* E)

@[expose] def hyperbolicForm :
    (Fin 2 → E) →ₛₗ[sigma.toRingHom] (Fin 2 → E) →ₗ[E] E :=
  CatalogueBHermitian.matrixForm sigma hyperbolicMatrix

theorem hyperbolicForm_apply (x y : Fin 2 → E) :
    hyperbolicForm sigma x y = sigma (x 0) * y 1 + sigma (x 1) * y 0 := by
  change herm sigma x (hyperbolicMatrix *ᵥ y) = _
  simp [herm, hyperbolicMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem hyperbolicForm_isSymm (hsigma : sigma ^ 2 = 1) :
    (hyperbolicForm sigma).IsSymm := by
  apply CatalogueBHermitian.matrixForm_isSymm sigma hsigma
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjTr, hyperbolicMatrix]

theorem hyperbolicForm_nondegenerate : (hyperbolicForm sigma).Nondegenerate :=
  CatalogueBHermitian.matrixForm_nondegenerate sigma hyperbolicGL

theorem exists_hyperbolic_isometry [Finite E]
    {V : Type v} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (h : V →ₛₗ[sigma.toRingHom] V →ₗ[E] E)
    (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (hdim : Module.finrank E V = 2) :
    ∃ B : (Fin 2 → E) ≃ₗ[E] V, ∀ x y, h (B x) (B y) = hyperbolicForm sigma x y := by
  exact CatalogueBHermitian.exists_isometry (hyperbolicForm sigma) h
    (hyperbolicForm_isSymm sigma hsigma) (hyperbolicForm_nondegenerate sigma)
    hsym hnd hsigma hne ((Module.finrank_fin_fun E).trans hdim.symm)

theorem hyperbolic_isometry_gram
    {V : Type v} [AddCommGroup V] [Module E V]
    (h : V →ₛₗ[sigma.toRingHom] V →ₗ[E] E)
    (B : (Fin 2 → E) ≃ₗ[E] V)
    (hB : ∀ x y, h (B x) (B y) = hyperbolicForm sigma x y) (i j : Fin 2) :
    h (B (Pi.single i 1)) (B (Pi.single j 1)) = hyperbolicMatrix i j := by
  rw [hB, hyperbolicForm_apply]
  fin_cases i <;> fin_cases j <;> simp [hyperbolicMatrix]

theorem exists_antifixed_unit (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) :
    ∃ t : Eˣ, sigma (t : E) = -(t : E) := by
  obtain ⟨z, hz⟩ := CatalogueBUnitaryNorm.exists_not_fixed sigma hne
  refine ⟨Units.mk0 (z - sigma z) (sub_ne_zero.mpr hz.symm), ?_⟩
  change sigma (z - sigma z) = -(z - sigma z)
  rw [map_sub, CatalogueBUnitaryNorm.involutive sigma hsigma]
  ring

theorem antifixed_iff_div_fixed (t : Eˣ) (ht : sigma (t : E) = -(t : E)) (x : E) :
    sigma x = -x ↔ sigma (x / (t : E)) = x / (t : E) := by
  rw [map_div₀, ht]
  constructor
  · intro hx
    rw [hx, neg_div_neg_eq]
  · intro hx
    have heq := (div_eq_div_iff (neg_ne_zero.mpr t.ne_zero) t.ne_zero).mp hx
    have heq' : (sigma x + x) * (t : E) = 0 := by linear_combination heq
    exact (add_eq_zero_iff_eq_neg).mp ((mul_eq_zero.mp heq').resolve_right t.ne_zero)

end CFSG.ComponentClassification.CatalogueBUnitaryTwo
