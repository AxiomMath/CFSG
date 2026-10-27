module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4NoPSpUGraph
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OILh
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUc

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIU

open Matrix Module CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut StabU DiagU ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatalogueBUnitaryB CFSG.LinearGroups
  CFSG.ComponentClassification.OddSelector
  CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] def gramQ {k : Type} [Field k] (δ : k) : Matrix (Fin 4) (Fin 4) k :=
  !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, -2, 0; 0, 0, 0, 2 * δ]

theorem gramQ_apply {k : Type} [Field k] (δ : k) (i j : Fin 4) :
    gramQ δ i j = OIL.qf δ (Pi.single i 1 + Pi.single j 1) - OIL.qf δ (Pi.single i 1) -
      OIL.qf δ (Pi.single j 1) := by
  fin_cases i <;> fin_cases j <;> simp [gramQ, OIL.qf] <;> ring

theorem exists_bar_neg : ∃ t : K, t ≠ 0 ∧ h.bar t = -t := by
  obtain ⟨t, ht, ht0⟩ := h.exists_mem_traceZero_ne_zero
  refine ⟨t, ht0, ?_⟩
  have h1 : h.trace t = 0 := ht
  rw [UnitaryFieldData.trace] at h1
  linear_combination h1

theorem exists_basis_matrix (hp2 : p ≠ 2) {A : Matrix (Fin 4) (Fin 4) K}
    (hAA : A * A.map h.bar = 1)
    (χ : (Fin 4 → h.fixedField) ≃ₗ[h.fixedField] fixW h A) :
    ∃ P : GL (Fin 4) K,
      (∀ x : Fin 4 → h.fixedField, (P : Matrix (Fin 4) (Fin 4) K) *ᵥ (fun i => (x i : K)) =
        ((χ x : fixW h A) : Fin 4 → K)) ∧
      (∀ i j, (P : Matrix (Fin 4) (Fin 4) K) i j =
        ((χ (Pi.single j 1) : fixW h A) : Fin 4 → K) i) ∧
      A * (P : Matrix (Fin 4) (Fin 4) K).map h.bar = P := by
  classical
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  obtain ⟨t, ht0, htb⟩ := exists_bar_neg h
  have hττ : ∀ v, (((1 : Kˣ) : K) • antiunitaryMap h A)
      ((((1 : Kˣ) : K) • antiunitaryMap h A) v) = v := by
    intro v
    simp only [Units.val_one, one_smul]
    rw [StabU.antiunitaryMap_sq h A (c := 1) (by rw [hAA, one_smul]), one_smul]
  let bW : Basis (Fin 4) h.fixedField (fixW h A) := (Pi.basisFun h.fixedField (Fin 4)).map χ
  let bK := conjFixedBasis hττ htb ht0 h2 bW
  have hbK : ∀ j, bK j = ((χ (Pi.single j 1) : fixW h A) : Fin 4 → K) := fun j => by
    change conjFixedBasis hττ htb ht0 h2 bW j = _
    rw [conjFixedBasis_apply, Basis.map_apply, Pi.basisFun_apply]
  let P : GL (Fin 4) K := ⟨(Pi.basisFun K (Fin 4)).toMatrix bK,
    bK.toMatrix (Pi.basisFun K (Fin 4)), Basis.toMatrix_mul_toMatrix_flip _ _,
    Basis.toMatrix_mul_toMatrix_flip _ _⟩
  have hPij : ∀ i j, (P : Matrix (Fin 4) (Fin 4) K) i j =
      ((χ (Pi.single j 1) : fixW h A) : Fin 4 → K) i := by
    intro i j
    change (Pi.basisFun K (Fin 4)).toMatrix bK i j = _
    rw [Basis.toMatrix_apply, Pi.basisFun_repr, hbK]
  refine ⟨P, fun x => ?_, hPij, ?_⟩
  · have hx : χ x = ∑ j, x j • χ (Pi.single j 1) := by
      conv_lhs => rw [← (Pi.basisFun h.fixedField (Fin 4)).sum_repr x]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, Pi.basisFun_repr, Pi.basisFun_apply]
    funext i
    rw [hx, Submodule.coe_sum, Finset.sum_apply]
    simp only [Matrix.mulVec, dotProduct, hPij, Submodule.coe_smul, Subfield.smul_def,
      Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · ext i j
    rw [hPij, Matrix.mul_apply]
    have hm := (mem_fixW h).mp (χ (Pi.single j 1)).2
    have e := congrFun hm i
    rw [← e]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hPij]

theorem gram_basis_matrix {A : Matrix (Fin 4) (Fin 4) K} (h2 : (2 : h.fixedField) ≠ 0)
    {δ : h.fixedFieldˣ} (ψW : fixW h A ≃ₗ[h.fixedField] hermitianSubmodule (δ : h.fixedField))
    (B' : LinearMap.BilinForm h.fixedField (fixW h A))
    (hB'v : ∀ v w, (B' v w : K) = stdHermForm h 4 v w) (hsym : B'.IsSymm) (d : h.fixedFieldˣ)
    (hψ : ∀ w, B' w w / 2 = (d : h.fixedField) * hermitianForm (δ : h.fixedField) (ψW w))
    (P : GL (Fin 4) K)
    (hPij : ∀ i j, (P : Matrix (Fin 4) (Fin 4) K) i j =
      ((((hermitianCoordinates (δ : h.fixedField) h2).trans ψW.symm) (Pi.single j 1) :
        fixW h A) : Fin 4 → K) i) :
    uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) =
      ((d : h.fixedField) : K) • (gramQ (δ : h.fixedField)).map h.fixedField.subtype := by
  set χ := (hermitianCoordinates (δ : h.fixedField) h2).trans ψW.symm with hχ
  have hψχ : ∀ x, ψW (χ x) = hermitianCoordinates (δ : h.fixedField) h2 x := fun x => by
    rw [hχ, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  have hpol : ∀ v w, B' v w = B' (v + w) (v + w) / 2 - B' v v / 2 - B' w w / 2 := by
    intro v w
    have hs : B' w v = B' v w := hsym.eq w v
    rw [LinearMap.map_add₂, LinearMap.map_add, LinearMap.map_add, hs]
    field_simp
    ring
  have hB : ∀ i j, B' (χ (Pi.single i 1)) (χ (Pi.single j 1)) =
      (d : h.fixedField) * gramQ (δ : h.fixedField) i j := by
    intro i j
    rw [hpol, ← map_add, hψ, hψ, hψ, hψχ, hψχ, hψχ, OIL.hermitianForm_coord,
      OIL.hermitianForm_coord, OIL.hermitianForm_coord, gramQ_apply]
    ring
  ext i j
  have e1 : (((d : h.fixedField) : K) • (gramQ (δ : h.fixedField)).map h.fixedField.subtype) i j =
      ((B' (χ (Pi.single i 1)) (χ (Pi.single j 1)) : h.fixedField) : K) := by
    rw [hB, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Subfield.coe_mul]
    rfl
  rw [e1, hB'v, stdHermForm_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [uStar, Matrix.transpose_apply, Matrix.map_apply, hPij, hPij]

end OIU

end CFSG.ComponentClassification.CatFactsL4U4
