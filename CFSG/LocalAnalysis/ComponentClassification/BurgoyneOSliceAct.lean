module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEmbed

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL compInd signMat
  commute_signMat_iff)
open scoped commutatorElement MatrixGroups

variable {K : Type} [Field K] {d : ℕ}

@[expose] def jSet : Finset (Fin d) := Finset.univ.filter fun i => (i : ℕ) < 2

theorem mem_jSet (i : Fin d) : i ∈ (jSet : Finset (Fin d)) ↔ (i : ℕ) < 2 := by
  simp [jSet]

theorem jSet_subset_wSet : (jSet : Finset (Fin d)) ⊆ wSet := by
  intro i hi
  rw [mem_jSet] at hi
  rw [mem_wSet]
  omega

@[expose] def qXGL {a : K} (ha : a ≠ 0) : GL (Fin 2) K :=
  ⟨!![0, a; -1, 0], !![0, -1; a⁻¹, 0], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [ha], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [ha]⟩

theorem coe_qXGL {a : K} (ha : a ≠ 0) :
    ((qXGL ha : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, a; -1, 0] := rfl

theorem coe_qXGL_inv {a : K} (ha : a ≠ 0) :
    (((qXGL ha)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, -1; a⁻¹, 0] := rfl

@[expose] def zSign {a : K} (ha : a ≠ 0) : equalDeterminants K :=
  ⟨(qXGL ha, -qXGL ha), by
    rw [mem_equalDeterminants, Units.val_neg, det_neg]
    simp⟩

@[expose] def sgn4 : Matrix (Fin 4) (Fin 4) K := diagonal ![-1, -1, 1, 1]

theorem qGamma_sign (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0)
    {X : CatalogueBGraphForm.isometryGroup 4 K (diagGL (qW_ne_zero ha))}
    (hX : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = sgn4) :
    qGamma h2 ha X = rho (zSign ha) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro M
  obtain ⟨x, rfl⟩ := (qEquiv h2 ha).surjective M
  change (qGamma h2 ha X).val (qEquiv h2 ha x) = (rho (zSign ha)).val (qEquiv h2 ha x)
  rw [qGamma_apply, rho_apply, hX]
  change qMat a (sgn4 *ᵥ x) = (qXGL ha : Matrix (Fin 2) (Fin 2) K) * qMat a x *
    (((-qXGL ha)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
  rw [inv_neg, Units.val_neg, coe_qXGL, coe_qXGL_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qMat, sgn4, Matrix.mul_apply, Fin.sum_univ_two, mulVec, dotProduct,
      diagonal] <;> field_simp <;> ring

theorem blk4_signMat_jSet (hd : 4 ≤ d) : blk4 hd (signMat K (jSet : Finset (Fin d))) = sgn4 := by
  ext i j
  rw [blk4_apply, signMat, diagonal_apply, sgn4, diagonal_apply]
  by_cases hij : i = j
  · subst hij
    fin_cases i <;> simp [mem_jSet]
  · have : (⟨i, by omega⟩ : Fin d) ≠ ⟨j, by omega⟩ := fun h => hij (Fin.ext (by simpa using h))
    simp [hij, this]

@[expose] def unipSL1 : SL(2, K) := ⟨!![1, 1; 0, 1], by simp [det_fin_two_of]⟩

theorem conjSL_qX_ne {a : K} (ha : a ≠ 0) : conjSL (qXGL ha) unipSL1 ≠ unipSL1 := by
  intro h
  have := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 0 1) h
  change ((conjSL (qXGL ha) unipSL1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 1 =
    ((unipSL1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 1 at this
  rw [coe_conjSL, coe_qXGL, coe_qXGL_inv] at this
  have hu : ((unipSL1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![1, 1; 0, 1] := rfl
  rw [hu] at this
  simp [Matrix.mul_apply, Fin.sum_univ_two] at this

theorem eq_scalar_of_conjSL_eq {A : GL (Fin 2) K} (hA : ∀ g : SL(2, K), conjSL A g = g) :
    ∃ c : Kˣ, A = GeneralLinearGroup.scalar (Fin 2) c := by
  have hcomm : ∀ g : SL(2, K), (A : Matrix (Fin 2) (Fin 2) K) * g =
      (g : Matrix (Fin 2) (Fin 2) K) * A := by
    intro g
    have e := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K)) (hA g)
    simp only [coe_conjSL] at e
    calc (A : Matrix (Fin 2) (Fin 2) K) * g = (A : Matrix (Fin 2) (Fin 2) K) * g *
        (((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * A) := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, e]
  set u₂ : SL(2, K) := ⟨!![1, 0; 1, 1], by simp [det_fin_two_of]⟩
  have e1 := hcomm unipSL1
  have e2 := hcomm u₂
  have h10 : (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    have := congrFun (congrFun e1 1) 1
    simpa [unipSL1, Matrix.mul_apply, Fin.sum_univ_two] using this
  have h01 : (A : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
    have := congrFun (congrFun e2 0) 0
    simpa [u₂, Matrix.mul_apply, Fin.sum_univ_two] using this
  have h11 : (A : Matrix (Fin 2) (Fin 2) K) 1 1 = (A : Matrix (Fin 2) (Fin 2) K) 0 0 := by
    have := congrFun (congrFun e1 0) 1
    simp [unipSL1, Matrix.mul_apply, Fin.sum_univ_two] at this
    linear_combination -this
  have h00 : (A : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := by
    intro h0
    have hdet := (Matrix.isUnits_det_units A).ne_zero
    rw [det_fin_two, h0, h01] at hdet
    simp at hdet
  refine ⟨Units.mk0 _ h00, Units.ext ?_⟩
  rw [GeneralLinearGroup.coe_scalar]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10, h01, h11]

end CFSG.ComponentClassification.Burgoyne.O
