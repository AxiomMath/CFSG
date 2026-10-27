module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddQuadraticWitt
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroBasic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalThreeSimilarity

open Matrix QuadraticMap CatalogueBOddQuadratic CatalogueBOrthogonal

universe u v

variable {K : Type u} [Field K]

@[expose] def planeLineToTraceZero (d : Kˣ) :
    ((Fin 1 → K × K) × (Fin 1 → K)) ≃ₗ[K] traceZeroSubmodule K where
  toFun x := traceZeroCoordinates K ![x.2 0, (x.1 0).1, (x.1 0).2 / (d : K)]
  invFun X := (fun _ => (X.val 0 1, (d : K) * X.val 1 0), fun _ => X.val 0 0)
  left_inv x := by
    apply Prod.ext
    · funext i
      fin_cases i
      apply Prod.ext
      · rfl
      · change (d : K) * ((x.1 0).2 / (d : K)) = (x.1 0).2
        field_simp
    · funext i
      fin_cases i
      rfl
  right_inv X := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · rfl
    · change (d : K) * X.val 1 0 / (d : K) = X.val 1 0
      field_simp
    · exact (traceZero_diagonal X).symm
  map_add' x y := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [traceZeroCoordinates, add_div]
    ring
  map_smul' a x := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [traceZeroCoordinates, smul_eq_mul, mul_div_assoc]

theorem planeLineToTraceZero_val (d : Kˣ)
    (x : (Fin 1 → K × K) × (Fin 1 → K)) :
    (planeLineToTraceZero d x).val =
      !![x.2 0, (x.1 0).1; (x.1 0).2 / (d : K), -x.2 0] := rfl

theorem planeLineToTraceZero_symm_apply (d : Kˣ) (X : traceZeroSubmodule K) :
    (planeLineToTraceZero d).symm X =
      (fun _ => (X.val 0 1, (d : K) * X.val 1 0), fun _ => X.val 0 0) := rfl

theorem planeLineToTraceZero_form (w : Fin 1 → Kˣ)
    (x : (Fin 1 → K × K) × (Fin 1 → K)) :
    ((hyperbolicSumForm K 1).prod (weightedSumSquares K w)) x =
      (w 0 : K) * traceZeroForm K (planeLineToTraceZero (w 0) x) := by
  rw [QuadraticMap.prod_apply, hyperbolicSumForm_apply, Fin.sum_univ_one,
    weightedSumSquares_apply, Fin.sum_univ_one, traceZeroForm_apply,
    planeLineToTraceZero_val]
  change (x.1 0).1 * (x.1 0).2 + (w 0 : K) * (x.2 0 * x.2 0) =
    (w 0 : K) * (x.2 0 * x.2 0 + (x.1 0).1 * ((x.1 0).2 / (w 0 : K)))
  field_simp
  ring

variable [Finite K] {V : Type v} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem exists_plane_line_isometry (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 3) :
    ∃ w : Fin 1 → Kˣ,
      Nonempty (Q.IsometryEquiv
        ((hyperbolicSumForm K 1).prod (weightedSumSquares K w))) := by
  obtain ⟨m, k, w, hk, _, hrank, he⟩ := exists_hyperbolic_decomposition hodd Q hQ
  have hm : m = 1 := by omega
  have hk' : k = 1 := by omega
  subst m
  subst k
  exact ⟨w, he⟩

theorem exists_trace_zero_similarity (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 3) :
    ∃ (d : Kˣ) (psi : V ≃ₗ[K] traceZeroSubmodule K),
      ∀ v, Q v = (d : K) * traceZeroForm K (psi v) := by
  obtain ⟨w, ⟨e⟩⟩ := exists_plane_line_isometry hodd Q hQ hdim
  refine ⟨w 0, e.toLinearEquiv.trans (planeLineToTraceZero (w 0)), ?_⟩
  intro v
  change Q v = (w 0 : K) * traceZeroForm K (planeLineToTraceZero (w 0) (e v))
  rw [← planeLineToTraceZero_form w (e v), e.map_app]

end CFSG.ComponentClassification.CatalogueBOrthogonalThreeSimilarity
