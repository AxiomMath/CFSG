module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixAction

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSix

open Matrix CatalogueBOrthogonalFourNonsplit

universe u

variable {K : Type u} [Field K]

@[expose] def sixExtensionSpan (delta : K) :
    Submodule (extension delta) (Matrix (Fin 4) (Fin 4) (extension delta)) :=
  Submodule.span (extension delta) (Set.range (fun X : sixSubmodule delta => X.val))

private theorem coordinate_mem_span (delta : K) (x : Fin 6 → K) :
    sixCoordinateMatrix delta x ∈ sixExtensionSpan delta :=
  Submodule.subset_span ⟨⟨_, sixCoordinateMatrix_mem delta x⟩, rfl⟩

private theorem skewMatrix_expansion {F : Type*} [CommRing F] (a b c d e f : F) :
    skewMatrix a b c d e f =
      a • skewMatrix 1 0 0 0 0 0 + b • skewMatrix 0 1 0 0 0 0 +
      c • skewMatrix 0 0 1 0 0 0 + d • skewMatrix 0 0 0 1 0 0 +
      e • skewMatrix 0 0 0 0 1 0 + f • skewMatrix 0 0 0 0 0 1 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [skewMatrix, smul_eq_mul]

private theorem six_span_basis (delta : K) [Fact (¬ IsSquare delta)] (h2 : (2 : K) ≠ 0) :
    (skewMatrix 1 0 0 0 0 0 : Matrix (Fin 4) (Fin 4) (extension delta)) ∈ sixExtensionSpan delta ∧
    (skewMatrix 0 1 0 0 0 0 : Matrix (Fin 4) (Fin 4) (extension delta)) ∈ sixExtensionSpan delta ∧
    (skewMatrix 0 0 1 0 0 0 : Matrix (Fin 4) (Fin 4) (extension delta)) ∈ sixExtensionSpan delta ∧
    (skewMatrix 0 0 0 1 0 0 : Matrix (Fin 4) (Fin 4) (extension delta)) ∈ sixExtensionSpan delta ∧
    (skewMatrix 0 0 0 0 1 0 : Matrix (Fin 4) (Fin 4) (extension delta)) ∈ sixExtensionSpan delta ∧
    (skewMatrix 0 0 0 0 0 1 : Matrix (Fin 4) (Fin 4) (extension delta)) ∈ sixExtensionSpan delta := by
  let t : extension delta := QuadraticAlgebra.omega
  have ht : t ≠ 0 := by
    intro h
    have hi := congrArg QuadraticAlgebra.im h
    simp [t] at hi
  have hz : (⟨0, 0⟩ : extension delta) = 0 := rfl
  have ho : (⟨1, 0⟩ : extension delta) = 1 := rfl
  have ht' : (⟨0, 1⟩ : extension delta) = t := rfl
  have hst : star t = -t := by
    apply QuadraticAlgebra.ext <;> simp [t]
  have hE2 := extension_two_ne_zero delta h2
  have h0 := coordinate_mem_span delta ![1, 0, 0, 0, 0, 0]
  have h1 := coordinate_mem_span delta ![0, 1, 0, 0, 0, 0]
  have h2' := coordinate_mem_span delta ![0, 0, 1, 0, 0, 0]
  have h3 := coordinate_mem_span delta ![0, 0, 0, 1, 0, 0]
  have h4 := coordinate_mem_span delta ![0, 0, 0, 0, 1, 0]
  have h5 := coordinate_mem_span delta ![0, 0, 0, 0, 0, 1]
  have hplus : (skewMatrix 0 1 0 0 1 0 : Matrix (Fin 4) (Fin 4) (extension delta)) ∈
      sixExtensionSpan delta := by simpa [sixCoordinateMatrix, conjugation, hz, ho] using h2'
  have hminus : (skewMatrix 0 1 0 0 (-1) 0 : Matrix (Fin 4) (Fin 4) (extension delta)) ∈
      sixExtensionSpan delta := by
    have h := (sixExtensionSpan delta).smul_mem t⁻¹ h3
    convert h using 1
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [sixCoordinateMatrix, skewMatrix, conjugation, hz, ht', hst, smul_eq_mul,
        inv_mul_cancel₀ ht]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [sixCoordinateMatrix, hz] using h0
  · have h := (sixExtensionSpan delta).smul_mem (2 : extension delta)⁻¹
      ((sixExtensionSpan delta).add_mem hplus hminus)
    convert h using 1
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [skewMatrix, smul_eq_mul] <;>
      field_simp <;> ring
  · have h := (sixExtensionSpan delta).smul_mem t⁻¹ h4
    convert h using 1
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [sixCoordinateMatrix, skewMatrix, hz, ht', smul_eq_mul, inv_mul_cancel₀ ht]
  · have h := (sixExtensionSpan delta).smul_mem t⁻¹ h5
    convert h using 1
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [sixCoordinateMatrix, skewMatrix, hz, ht', smul_eq_mul, inv_mul_cancel₀ ht]
  · have h := (sixExtensionSpan delta).smul_mem (2 : extension delta)⁻¹
      ((sixExtensionSpan delta).sub_mem hplus hminus)
    convert h using 1
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [skewMatrix, smul_eq_mul] <;>
      field_simp <;> ring
  · simpa [sixCoordinateMatrix, hz] using h1

theorem sixExtensionSpan_eq_skew (delta : K) [Fact (¬ IsSquare delta)] (h2 : (2 : K) ≠ 0) :
    sixExtensionSpan delta = skewSubmodule (extension delta) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨X, rfl⟩
    exact X.property.1
  · intro X hX
    obtain ⟨h0, h1, h2', h3, h4, h5⟩ := six_span_basis delta h2
    rw [skew_eq_skewMatrix (extension_two_ne_zero delta h2) hX, skewMatrix_expansion]
    exact (sixExtensionSpan delta).add_mem
      ((sixExtensionSpan delta).add_mem
        ((sixExtensionSpan delta).add_mem
          ((sixExtensionSpan delta).add_mem
            ((sixExtensionSpan delta).add_mem
              ((sixExtensionSpan delta).smul_mem _ h0) ((sixExtensionSpan delta).smul_mem _ h1))
            ((sixExtensionSpan delta).smul_mem _ h2'))
          ((sixExtensionSpan delta).smul_mem _ h3))
        ((sixExtensionSpan delta).smul_mem _ h4))
      ((sixExtensionSpan delta).smul_mem _ h5)

theorem sixSpecial_fixed_skew (delta : K) [Fact (¬ IsSquare delta)] (h2 : (2 : K) ≠ 0)
    (g : sixSpecialUnitary delta) (hg : sixSpecialKappa delta h2 g = 1)
    (X : Matrix (Fin 4) (Fin 4) (extension delta)) (hX : X.transpose = -X) :
    g.val.val * X * g.val.val.transpose = X := by
  have hspan : X ∈ sixExtensionSpan delta := by rw [sixExtensionSpan_eq_skew delta h2]; exact hX
  clear hX
  induction hspan using Submodule.span_induction with
  | mem Y hY =>
    obtain ⟨Y, rfl⟩ := hY
    have h := congrArg (fun a : SixIsometries delta => (a.val Y).val) hg
    change ((sixSpecialKappa delta h2 g).val Y).val = Y.val at h
    exact (sixSpecialKappa_val delta h2 g Y).symm.trans h
  | zero => simp
  | add Y Z _ _ hY hZ => rw [Matrix.mul_add, Matrix.add_mul, hY, hZ]
  | smul a Y _ hY => rw [Matrix.mul_smul, Matrix.smul_mul, hY]

end CFSG.ComponentClassification.CatalogueBOrthogonalSix
