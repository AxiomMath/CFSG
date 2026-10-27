module

public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

namespace CFSG.GH74.Generic.S1.Exo

open Module
open scoped Matrix

variable {F : Type} [Field F]

@[expose] def uniDescSigma (bar : F →+* F) (g : Matrix (Fin 4) (Fin 4) F) (v : Fin 4 → F) :
    Fin 4 → F :=
  g.mulVec (fun i => bar (v i))

theorem uniDescSigma_add (bar : F →+* F) (g : Matrix (Fin 4) (Fin 4) F) (v w : Fin 4 → F) :
    uniDescSigma bar g (v + w) = uniDescSigma bar g v + uniDescSigma bar g w := by
  simp only [uniDescSigma, Pi.add_apply, map_add]
  rw [show (fun i => bar (v i) + bar (w i)) = (fun i => bar (v i)) + (fun i => bar (w i)) from rfl,
    Matrix.mulVec_add]

theorem uniDescSigma_sub (bar : F →+* F) (g : Matrix (Fin 4) (Fin 4) F) (v w : Fin 4 → F) :
    uniDescSigma bar g (v - w) = uniDescSigma bar g v - uniDescSigma bar g w := by
  simp only [uniDescSigma, Pi.sub_apply, map_sub]
  rw [show (fun i => bar (v i) - bar (w i)) = (fun i => bar (v i)) - (fun i => bar (w i)) from rfl,
    Matrix.mulVec_sub]

theorem uniDescSigma_smul (bar : F →+* F) (g : Matrix (Fin 4) (Fin 4) F) (c : F) (v : Fin 4 → F) :
    uniDescSigma bar g (c • v) = bar c • uniDescSigma bar g v := by
  simp only [uniDescSigma, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [show (fun i => bar c * bar (v i)) = bar c • (fun i => bar (v i)) from rfl, Matrix.mulVec_smul]

theorem uniDescSigma_sigma (bar : F →+* F) (hbb : ∀ x, bar (bar x) = x)
    (g : Matrix (Fin 4) (Fin 4) F) (hgg : g * g.map bar = 1) (v : Fin 4 → F) :
    uniDescSigma bar g (uniDescSigma bar g v) = v := by
  have h1 : (fun i => bar (uniDescSigma bar g v i)) = (g.map bar).mulVec v := by
    ext i
    simp only [uniDescSigma, Matrix.mulVec, dotProduct, map_sum, map_mul, hbb, Matrix.map_apply]
  rw [uniDescSigma, h1, Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]

theorem uniDescSigma_span (bar : F →+* F) (hbb : ∀ x, bar (bar x) = x) (h2 : (2 : F) ≠ 0) {δ : F}
    (hδ0 : δ ≠ 0) (hδ : bar δ = -δ) (g : Matrix (Fin 4) (Fin 4) F) (hgg : g * g.map bar = 1) :
    Submodule.span F {v : Fin 4 → F | uniDescSigma bar g v = v} = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have ha : uniDescSigma bar g (v + uniDescSigma bar g v) = v + uniDescSigma bar g v := by
    rw [uniDescSigma_add, uniDescSigma_sigma bar hbb g hgg, add_comm]
  have hb : uniDescSigma bar g (δ⁻¹ • (v - uniDescSigma bar g v)) =
      δ⁻¹ • (v - uniDescSigma bar g v) := by
    rw [uniDescSigma_smul, uniDescSigma_sub, uniDescSigma_sigma bar hbb g hgg, map_inv₀, hδ,
      inv_neg, neg_smul, ← smul_neg, neg_sub]
  have hv : v = (2⁻¹ : F) • (v + uniDescSigma bar g v) +
      (2⁻¹ * δ) • (δ⁻¹ • (v - uniDescSigma bar g v)) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    ring
  rw [hv]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ha))
    (Submodule.smul_mem _ _ (Submodule.subset_span hb))

theorem uniDesc_exists_basis (bar : F →+* F) (hbb : ∀ x, bar (bar x) = x) (h2 : (2 : F) ≠ 0)
    {δ : F} (hδ0 : δ ≠ 0) (hδ : bar δ = -δ) (g : Matrix (Fin 4) (Fin 4) F)
    (hgg : g * g.map bar = 1) :
    ∃ B : Basis (Fin 4) F (Fin 4 → F), ∀ i, uniDescSigma bar g (B i) = B i := by
  obtain ⟨b, hbS, hbspan, hbli⟩ :=
    exists_linearIndependent F {v : Fin 4 → F | uniDescSigma bar g v = v}
  have hbtop : ⊤ ≤ Submodule.span F (Set.range (Subtype.val : b → (Fin 4 → F))) := by
    rw [Subtype.range_coe, hbspan, uniDescSigma_span bar hbb h2 hδ0 hδ g hgg]
  let B0 : Basis b F (Fin 4 → F) := Basis.mk hbli hbtop
  have hfin : Finite b := Module.Finite.finite_basis B0
  have hcard : Nat.card b = 4 := by
    rw [← Module.finrank_eq_nat_card_basis B0, Module.finrank_fin_fun]
  let e : b ≃ Fin 4 := Finite.equivFinOfCardEq hcard
  refine ⟨B0.reindex e, fun i => ?_⟩
  rw [Basis.reindex_apply, Basis.mk_apply]
  exact hbS (e.symm i).2

theorem uniDesc_exists_P (bar : F →+* F) (hbb : ∀ x, bar (bar x) = x) (h2 : (2 : F) ≠ 0) {δ : F}
    (hδ0 : δ ≠ 0) (hδ : bar δ = -δ) (g : Matrix (Fin 4) (Fin 4) F) (hgg : g * g.map bar = 1) :
    ∃ P : Matrix (Fin 4) (Fin 4) F, IsUnit P.det ∧ g * P.map bar = P := by
  obtain ⟨B, hB⟩ := uniDesc_exists_basis bar hbb h2 hδ0 hδ g hgg
  let P : Matrix (Fin 4) (Fin 4) F := (Pi.basisFun F (Fin 4)).toMatrix B
  have hPij : ∀ i j, P i j = B j i := by
    intro i j
    simp [P, Basis.toMatrix_apply]
  have hinv : Invertible P := (Pi.basisFun F (Fin 4)).invertibleToMatrix B
  refine ⟨P, (Matrix.isUnit_iff_isUnit_det P).1 (isUnit_of_invertible P), ?_⟩
  ext i j
  have := congrFun (hB j) i
  simp only [uniDescSigma, Matrix.mulVec, dotProduct] at this
  simp only [Matrix.mul_apply, Matrix.map_apply, hPij]
  exact this

end CFSG.GH74.Generic.S1.Exo
