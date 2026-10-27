module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveSimilitudes
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalFive

open Matrix QuadraticMap

universe u

variable {K : Type u} [Field K]

theorem selfAdjoint_conjugate_equation (A : symplecticSimilitudes K)
    (X : selfAdjointSubmodule K) :
    (A.val.val * X.val * A.val⁻¹.val)ᵀ * symplecticGram K =
      symplecticGram K * (A.val.val * X.val * A.val⁻¹.val) := by
  let g := A.val
  let a : Kˣ := symplecticMultiplier A
  have hg : g.valᵀ * symplecticGram K * g.val = (a : K) • symplecticGram K :=
    symplecticMultiplier_spec A
  have hgt : g.valᵀ * g⁻¹.valᵀ = 1 := by
    rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
  have hinvt : g⁻¹.valᵀ * g.valᵀ = 1 := by
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have h : g.valᵀ * ((g.val * X.val * g⁻¹.val)ᵀ * symplecticGram K) * g.val =
      g.valᵀ * (symplecticGram K * (g.val * X.val * g⁻¹.val)) * g.val := by
    calc
      g.valᵀ * ((g.val * X.val * g⁻¹.val)ᵀ * symplecticGram K) * g.val =
          X.valᵀ * (g.valᵀ * symplecticGram K * g.val) := by
            simp only [Matrix.transpose_mul, ← Matrix.mul_assoc, hgt, Matrix.one_mul]
      _ = (a : K) • (X.valᵀ * symplecticGram K) := by rw [hg, Matrix.mul_smul]
      _ = (a : K) • (symplecticGram K * X.val) := by rw [X.property.1]
      _ = (g.valᵀ * symplecticGram K * g.val) * X.val := by rw [hg, Matrix.smul_mul]
      _ = g.valᵀ * (symplecticGram K * (g.val * X.val * g⁻¹.val)) * g.val := by
        simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have cancel (M : Matrix (Fin 4) (Fin 4) K) :
      g⁻¹.valᵀ * (g.valᵀ * M * g.val) * g⁻¹.val = M := by
    calc
      _ = (g⁻¹.valᵀ * g.valᵀ) * M * (g.val * g⁻¹.val) := by
        simp only [Matrix.mul_assoc]
      _ = M := by rw [hinvt, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]
  have hc := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => g⁻¹.valᵀ * M * g⁻¹.val) h
  rw [cancel, cancel] at hc
  exact hc

@[expose] def selfAdjointConjugation (A : symplecticSimilitudes K) :
    selfAdjointSubmodule K ≃ₗ[K] selfAdjointSubmodule K where
  toFun X := ⟨A.val.val * X.val * A.val⁻¹.val,
    selfAdjoint_conjugate_equation A X,
    (Matrix.trace_units_conj A.val X.val).trans X.property.2⟩
  invFun X := ⟨A.val⁻¹.val * X.val * A.val.val, by
    have h := selfAdjoint_conjugate_equation A⁻¹ X
    simpa only [Subgroup.coe_inv, inv_inv] using h,
    (Matrix.trace_units_conj' A.val X.val).trans X.property.2⟩
  left_inv X := by
    apply Subtype.ext
    change A.val⁻¹.val * (A.val.val * X.val * A.val⁻¹.val) * A.val.val = X.val
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc A.val⁻¹.val A.val.val,
      Units.inv_mul, Matrix.one_mul, Matrix.mul_one]
  right_inv X := by
    apply Subtype.ext
    change A.val.val * (A.val⁻¹.val * X.val * A.val.val) * A.val⁻¹.val = X.val
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc A.val.val A.val⁻¹.val,
      Units.mul_inv, Matrix.one_mul, Matrix.mul_one]
  map_add' X Y := by
    apply Subtype.ext
    change A.val.val * (X.val + Y.val) * A.val⁻¹.val = _
    rw [Matrix.mul_add, Matrix.add_mul]
    rfl
  map_smul' a X := by
    apply Subtype.ext
    change A.val.val * (a • X.val) * A.val⁻¹.val = _
    rw [Matrix.mul_smul, Matrix.smul_mul]
    rfl

theorem selfAdjointConjugation_val (A : symplecticSimilitudes K) (X : selfAdjointSubmodule K) :
    (selfAdjointConjugation A X).val = A.val.val * X.val * A.val⁻¹.val := rfl

theorem selfAdjointConjugation_form (h2 : (2 : K) ≠ 0)
    (A : symplecticSimilitudes K) (X : selfAdjointSubmodule K) :
    selfAdjointForm K (selfAdjointConjugation A X) = selfAdjointForm K X := by
  have h := selfAdjoint_square h2 (selfAdjointConjugation A X)
  rw [selfAdjointConjugation_val] at h
  have hsq :
      (A.val.val * X.val * A.val⁻¹.val) * (A.val.val * X.val * A.val⁻¹.val) =
        selfAdjointForm K X • (1 : Matrix (Fin 4) (Fin 4) K) := by
    calc
      _ = A.val.val * (X.val * X.val) * A.val⁻¹.val := by
        calc
          _ = A.val.val * (X.val * (A.val⁻¹.val * A.val.val) * X.val) * A.val⁻¹.val := by
            simp only [Matrix.mul_assoc]
          _ = _ := by rw [Units.inv_mul, Matrix.mul_one]
      _ = _ := by rw [selfAdjoint_square h2, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, Units.mul_inv]
  have hc := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 0 0) (h.symm.trans hsq)
  simpa only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] using hc

@[expose] def selfAdjointOrthogonalAction (h2 : (2 : K) ≠ 0) :
    symplecticSimilitudes K →* TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K) where
  toFun A := ⟨selfAdjointConjugation A,
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (selfAdjointConjugation_form h2 A)⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro X
    apply Subtype.ext
    simp [selfAdjointConjugation_val]
  map_mul' A B := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro X
    apply Subtype.ext
    change (A.val * B.val).val * X.val * (A.val * B.val)⁻¹.val =
      A.val.val * (B.val.val * X.val * B.val⁻¹.val) * A.val⁻¹.val
    simp only [Units.val_mul, _root_.mul_inv_rev, Matrix.mul_assoc]

theorem selfAdjointOrthogonalAction_val (h2 : (2 : K) ≠ 0)
    (A : symplecticSimilitudes K) (X : selfAdjointSubmodule K) :
    ((selfAdjointOrthogonalAction h2 A).val X).val =
      A.val.val * X.val * A.val⁻¹.val := rfl

end CFSG.ComponentClassification.CatalogueBOrthogonalFive
