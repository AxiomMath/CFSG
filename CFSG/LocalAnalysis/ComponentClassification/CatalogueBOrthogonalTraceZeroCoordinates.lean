module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroProjective
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoCentralizer

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonal

open Matrix QuadraticMap CatalogueBLinearTwo CatalogueSchreierLinearTwo

universe u

variable {K : Type u} [Field K]

@[expose] def traceZeroCoordinateToProjective :
    coordinateD K × rootsOfUnity 2 K ≃*
      ProjGenLinGroup (Fin 2) K × rootsOfUnity 2 K where
  toFun x := ((pglEquivCoordinateD_all_fields K).symm x.1, x.2)
  invFun x := (pglEquivCoordinateD_all_fields K x.1, x.2)
  left_inv x := Prod.ext ((pglEquivCoordinateD_all_fields K).apply_symm_apply x.1) rfl
  right_inv x := Prod.ext ((pglEquivCoordinateD_all_fields K).symm_apply_apply x.1) rfl
  map_mul' x y := Prod.ext (map_mul (pglEquivCoordinateD_all_fields K).symm x.1 y.1) rfl

@[expose] def traceZeroCoordinateEquiv (h2 : (2 : K) ≠ 0) :
    coordinateD K × rootsOfUnity 2 K ≃*
      TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm K) :=
  traceZeroCoordinateToProjective.trans (traceZeroProjectiveEquiv h2)

theorem traceZero_coordinate_representative (A : GL (Fin 2) K) :
    (pglEquivCoordinateD_all_fields K (ProjGenLinGroup.mk A)).val =
      coordinateGLAction K A := rfl

theorem traceZeroCoordinateEquiv_val (h2 : (2 : K) ≠ 0) (A : GL (Fin 2) K)
    (ε : rootsOfUnity 2 K) (X : traceZeroSubmodule K) :
    ((traceZeroCoordinateEquiv h2
      (pglEquivCoordinateD_all_fields K (ProjGenLinGroup.mk A), ε)).val X).val =
        (ε.val : K) • (A.val * X.val * A⁻¹.val) := by
  change ((traceZeroProjectiveEquiv h2
    ((pglEquivCoordinateD_all_fields K).symm
      (pglEquivCoordinateD_all_fields K (ProjGenLinGroup.mk A)), ε)).val X).val = _
  rw [(pglEquivCoordinateD_all_fields K).symm_apply_apply]
  exact traceZeroProjectiveEquiv_val h2 A ε X

theorem traceZeroCoordinateEquiv_representative_val (h2 : (2 : K) ≠ 0)
    (d : coordinateD K) (A : GL (Fin 2) K)
    (hA : coordinateGLAction K A = d.val) (ε : rootsOfUnity 2 K)
    (X : traceZeroSubmodule K) :
    ((traceZeroCoordinateEquiv h2 (d, ε)).val X).val =
      (ε.val : K) • (A.val * X.val * A⁻¹.val) := by
  have hd : pglEquivCoordinateD_all_fields K (ProjGenLinGroup.mk A) = d :=
    Subtype.ext hA
  rw [← hd]
  exact traceZeroCoordinateEquiv_val h2 A ε X

theorem trace_zero_three_full_orthogonal_isometry (h2 : (2 : K) ≠ 0) :
    ∃ e : coordinateD K × rootsOfUnity 2 K ≃*
      TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm K),
      ∀ (d : coordinateD K) (ε : rootsOfUnity 2 K) (A : GL (Fin 2) K),
        coordinateGLAction K A = d.val → ∀ X : traceZeroSubmodule K,
          ((e (d, ε)).val X).val = (ε.val : K) • (A.val * X.val * A⁻¹.val) := by
  refine ⟨traceZeroCoordinateEquiv h2, ?_⟩
  intro d ε A hA X
  exact traceZeroCoordinateEquiv_representative_val h2 d A hA ε X

end CFSG.ComponentClassification.CatalogueBOrthogonal
