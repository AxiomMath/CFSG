module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L2Ord
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L2Ord

open Matrix Polynomial
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem trace_inv_conj (M : Matrix.SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F) (s : F) :
    ((M⁻¹ * (gSL s v * M * (gSL s v)⁻¹) : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F).trace = 2 + (s * cycQ M v) ^ 2 := by
  obtain ⟨a, b, c, d, hM⟩ : ∃ a b c d : F, (M : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdet : (M : Matrix (Fin 2) (Fin 2) F).det = 1 := M.2
  rw [hM, Matrix.det_fin_two_of] at hdet
  have hg : ((gSL s v : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      gMat s v := rfl
  have hg' : (((gSL s v)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      gMat (-s) v := by
    rw [gSL_inv]
    rfl
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [hg, hg', Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, hM]
  simp [gMat, Matrix.trace_fin_two, cycQ]
  linear_combination 2 * hdet

theorem trace_mul_conj (M : Matrix.SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F) (s : F) :
    ((M * (gSL s v * M * (gSL s v)⁻¹) : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F).trace =
        (M : Matrix (Fin 2) (Fin 2) F).trace ^ 2 - 2 - (s * cycQ M v) ^ 2 := by
  obtain ⟨a, b, c, d, hM⟩ : ∃ a b c d : F, (M : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdet : (M : Matrix (Fin 2) (Fin 2) F).det = 1 := M.2
  rw [hM, Matrix.det_fin_two_of] at hdet
  have hg : ((gSL s v : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      gMat s v := rfl
  have hg' : (((gSL s v)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      gMat (-s) v := by
    rw [gSL_inv]
    rfl
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [hg, hg', hM]
  simp [gMat, Matrix.trace_fin_two, cycQ]
  linear_combination (-2) * hdet

theorem exists_cycQ_ne_zero (M : Matrix (Fin 2) (Fin 2) F) (hM : ∀ c : F, M ≠ c • 1) :
    ∃ v : Fin 2 → F, cycQ M v ≠ 0 := by
  by_cases h10 : M 1 0 = 0
  · by_cases h01 : M 0 1 = 0
    · by_cases hd : M 1 1 = M 0 0
      · exfalso
        apply hM (M 0 0)
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h10, h01, hd]
      · exact ⟨![1, 1], by simpa [cycQ, h10, h01] using sub_ne_zero.mpr hd⟩
    · exact ⟨![0, 1], by simpa [cycQ] using h01⟩
  · exact ⟨![1, 0], by simpa [cycQ] using h10⟩

@[expose] noncomputable def ordPolyX : F[X] :=
  (X ^ 2 - C 4) * X * (X ^ 2 - C 1) * (X ^ 4 - C 3 * X ^ 2 + C 1)

theorem eval_ordPolyX (τ : F) : ordPolyX.eval τ = ordPoly τ := by
  simp [ordPolyX, ordPoly]

theorem natDegree_ordPolyX : (ordPolyX : F[X]).natDegree = 9 := by
  unfold ordPolyX
  compute_degree!

theorem exists_t_of_card [Finite F] (hF : 19 ≤ Nat.card F) : ∃ t : F, ordPoly (2 + t ^ 2) ≠ 0 := by
  classical
  have := Fintype.ofFinite F
  by_contra hcon
  push Not at hcon
  set Q : F[X] := ordPolyX.comp (X ^ 2 + C 2) with hQ
  have hdeg : Q.natDegree = 18 := by
    rw [hQ, natDegree_comp, natDegree_ordPolyX]
    have : (X ^ 2 + C 2 : F[X]).natDegree = 2 := by compute_degree!
    rw [this]
  have hQ0 : Q = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' Q Finset.univ ?_ ?_
    · rintro t -
      rw [hQ, eval_comp, eval_ordPolyX]
      simpa [add_comm] using hcon t
    · rw [hdeg, Finset.card_univ, ← Nat.card_eq_fintype_card]
      omega
  rw [hQ0] at hdeg
  simp at hdeg

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L2Ord
