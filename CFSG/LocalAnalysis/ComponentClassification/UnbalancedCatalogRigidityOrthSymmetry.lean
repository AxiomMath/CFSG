module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalRealization

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer (mem_matrixDerived_iff)
open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] {d : ℕ}

@[expose] def symmetryGL (Q : QuadraticForm K (Fin d → K)) (v : Fin d → K) : GL (Fin d) K :=
  matrixLinearIso.symm (reflect Q v)

variable {Q : QuadraticForm K (Fin d → K)} {v : Fin d → K}

theorem matrixLinearIso_symmetryGL : matrixLinearIso (symmetryGL Q v) = reflect Q v :=
  matrixLinearIso.apply_symm_apply _

theorem symmetryGL_mulVec (x : Fin d → K) :
    (symmetryGL Q v : Matrix (Fin d) (Fin d) K) *ᵥ x = reflect Q v x := by
  rw [← matrixLinearIso_symmetryGL]
  rfl

theorem symmetryGL_mulVec_of_charTwo [CharP K 2] (hv : Q v = 1) (x : Fin d → K) :
    (symmetryGL Q v : Matrix (Fin d) (Fin d) K) *ᵥ x = x + polar Q v x • v := by
  rw [symmetryGL_mulVec, reflect_apply (by rw [hv]; exact one_ne_zero), hv, div_one,
    sub_eq_add_neg, ← neg_smul, CharTwo.neg_eq]

theorem symmetryGL_mem (Q : QuadraticForm K (Fin d → K)) (v : Fin d → K) :
    symmetryGL Q v ∈ matrixIsometries Q := by
  change matrixLinearIso (symmetryGL Q v) ∈ TauCeti.QuadraticMap.orthogonalGroup Q
  rw [matrixLinearIso_symmetryGL]
  exact reflect_mem_orthogonalGroup Q v

theorem symmetryGL_mul_self (Q : QuadraticForm K (Fin d → K)) (v : Fin d → K) :
    symmetryGL Q v * symmetryGL Q v = 1 := by
  apply matrixLinearIso.injective
  rw [map_mul, matrixLinearIso_symmetryGL, reflect_mul_self, map_one]

theorem conj_symmetryGL {g : GL (Fin d) K} (hg : g ∈ matrixIsometries Q) :
    g * symmetryGL Q v * g⁻¹ = symmetryGL Q ((g : Matrix (Fin d) (Fin d) K) *ᵥ v) := by
  have hg' : matrixLinearIso g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := hg
  apply matrixLinearIso.injective
  rw [map_mul, map_mul, map_inv, matrixLinearIso_symmetryGL, matrixLinearIso_symmetryGL,
    reflect_conj hg']
  rfl

theorem eq_of_symmetryGL_eq [CharP K 2] (hQ : Q.polarBilin.Nondegenerate) {a b : Fin d → K}
    (ha : Q a = 1) (hb : Q b = 1) (h : symmetryGL Q a = symmetryGL Q b) : a = b := by
  have hx : ∀ x, polar Q a x • a = polar Q b x • b := fun x => by
    have := congrArg (fun A : GL (Fin d) K => (A : Matrix (Fin d) (Fin d) K) *ᵥ x) h
    simpa only [symmetryGL_mulVec_of_charTwo ha, symmetryGL_mulVec_of_charTwo hb,
      add_right_inj] using this
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hb
    exact zero_ne_one hb
  obtain ⟨x, hxb⟩ : ∃ x, polar Q b x ≠ 0 := by
    by_contra! h0
    exact hb0 (hQ.1 b fun y => by rw [QuadraticMap.polarBilin_apply_apply]; exact h0 y)
  have h1 : b = (polar Q a x / polar Q b x) • a := by
    rw [div_eq_inv_mul, mul_smul, hx, smul_smul, inv_mul_cancel₀ hxb, one_smul]
  have h2 : (polar Q a x / polar Q b x) ^ 2 = 1 := by
    have := congrArg Q h1
    rwa [QuadraticMap.map_smul, ha, hb, smul_eq_mul, mul_one, ← _root_.sq, eq_comm] at this
  have h3 : polar Q a x / polar Q b x = 1 := by
    have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
    have h4 : (polar Q a x / polar Q b x - 1) ^ 2 = 0 := by
      linear_combination h2 + (1 - polar Q a x / polar Q b x) * h22
    exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h4)
  rw [h1, h3, one_smul]

theorem mem_centralizer_symmetryGL_iff [CharP K 2] (hQ : Q.polarBilin.Nondegenerate)
    (hv : Q v = 1) {g : GL (Fin d) K} (hg : g ∈ matrixIsometries Q) :
    g ∈ Subgroup.centralizer {symmetryGL Q v} ↔ (g : Matrix (Fin d) (Fin d) K) *ᵥ v = v := by
  have hgv : Q ((g : Matrix (Fin d) (Fin d) K) *ᵥ v) = 1 := by
    rw [← hv]
    exact (mem_matrixIsometries_iff Q g).mp hg v
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 : g * symmetryGL Q v * g⁻¹ = symmetryGL Q v := by rw [h, mul_inv_cancel_right]
    rw [conj_symmetryGL hg] at h1
    exact eq_of_symmetryGL_eq hQ hgv hv h1
  · intro h
    have h1 := conj_symmetryGL (v := v) hg
    rw [h] at h1
    calc g * symmetryGL Q v = g * symmetryGL Q v * g⁻¹ * g := by group
      _ = symmetryGL Q v * g := by rw [h1]

theorem polar_coordinateSemilinearMap {g : similarityPairs Q}
    (hg : g ∈ UnitaryHigher.unitMultiplierPairs Q) (x y : Fin d → K) :
    polar Q (coordinateSemilinearMap g.val x) (coordinateSemilinearMap g.val y) =
      g.val.right (polar Q x y) := by
  have hQg := (UnitaryHigher.mem_unitMultiplierPairs_iff Q g).mp hg
  simp only [polar, ← map_add, hQg, map_sub]

theorem semilinear_apply_eq_of_commute_symmetry [CharP K 2] (hQ : Q.polarBilin.Nondegenerate)
    (hv : Q v = 1) {g : similarityPairs Q} (hg : g ∈ UnitaryHigher.unitMultiplierPairs Q)
    (hcomm : ∀ x, coordinateSemilinearMap g.val
      ((symmetryGL Q v : Matrix (Fin d) (Fin d) K) *ᵥ x) =
        (symmetryGL Q v : Matrix (Fin d) (Fin d) K) *ᵥ coordinateSemilinearMap g.val x) :
    coordinateSemilinearMap g.val v = v := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hv
    exact zero_ne_one hv
  obtain ⟨x, hx⟩ : ∃ x, polar Q v x = 1 := by
    obtain ⟨y, hy⟩ : ∃ y, polar Q v y ≠ 0 := by
      by_contra! h0
      exact hv0 (hQ.1 v fun y => by rw [QuadraticMap.polarBilin_apply_apply]; exact h0 y)
    refine ⟨(polar Q v y)⁻¹ • y, ?_⟩
    rw [polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hy]
  have h1 := hcomm x
  rw [symmetryGL_mulVec_of_charTwo hv, symmetryGL_mulVec_of_charTwo hv, map_add,
    coordinateSemilinearMap_smul, hx, map_one, one_smul, add_right_inj] at h1
  set c := polar Q v (coordinateSemilinearMap g.val x) with hc
  have hQS : Q (coordinateSemilinearMap g.val v) = 1 := by
    rw [(UnitaryHigher.mem_unitMultiplierPairs_iff Q g).mp hg, hv, map_one]
  rw [h1, QuadraticMap.map_smul, hv, smul_eq_mul, mul_one] at hQS
  have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h4 : (c - 1) ^ 2 = 0 := by linear_combination hQS + (1 - c) * h22
  rw [h1, sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h4), one_smul]

end CFSG.ComponentClassification.UnbalancedCatalog
