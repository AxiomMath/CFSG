module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEAlg
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneORes
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSliceAct
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSliceDef

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open scoped MatrixGroups

variable {K : Type} [Field K] {d : ℕ}

@[expose] def qLeftMat (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) (P : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 4) (Fin 4) K :=
  LinearMap.toMatrix' ((qEquiv h2 ha).symm.toLinearMap ∘ₗ
    (LinearMap.mulLeft K P) ∘ₗ (qEquiv h2 ha).toLinearMap)

theorem qLeftMat_mulVec (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) (P : Matrix (Fin 2) (Fin 2) K)
    (x : Fin 4 → K) : qLeftMat h2 ha P *ᵥ x = (qEquiv h2 ha).symm (P * qEquiv h2 ha x) := by
  rw [qLeftMat, LinearMap.toMatrix'_mulVec]
  rfl

theorem qLeftMat_mul (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) (P P' : Matrix (Fin 2) (Fin 2) K) :
    qLeftMat h2 ha (P * P') = qLeftMat h2 ha P * qLeftMat h2 ha P' := by
  refine (Matrix.toLin' (R := K)).injective (LinearMap.ext fun x => ?_)
  rw [Matrix.toLin'_apply, Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_apply,
    Matrix.toLin'_apply, qLeftMat_mulVec, qLeftMat_mulVec, qLeftMat_mulVec,
    LinearEquiv.apply_symm_apply, Matrix.mul_assoc]

theorem qLeftMat_one (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) : qLeftMat h2 ha 1 = 1 := by
  refine (Matrix.toLin' (R := K)).injective (LinearMap.ext fun x => ?_)
  rw [Matrix.toLin'_apply, qLeftMat_mulVec, Matrix.one_mul, LinearEquiv.symm_apply_apply,
    Matrix.toLin'_one]
  rfl

theorem qLeftMat_add (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) (P P' : Matrix (Fin 2) (Fin 2) K) :
    qLeftMat h2 ha (P + P') = qLeftMat h2 ha P + qLeftMat h2 ha P' := by
  refine (Matrix.toLin' (R := K)).injective (LinearMap.ext fun x => ?_)
  rw [Matrix.toLin'_apply, map_add, LinearMap.add_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
    qLeftMat_mulVec, qLeftMat_mulVec, qLeftMat_mulVec, Matrix.add_mul, map_add]

theorem qLeftMat_smul (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) (r : K)
    (P : Matrix (Fin 2) (Fin 2) K) : qLeftMat h2 ha (r • P) = r • qLeftMat h2 ha P := by
  refine (Matrix.toLin' (R := K)).injective (LinearMap.ext fun x => ?_)
  rw [Matrix.toLin'_apply, map_smul, LinearMap.smul_apply, Matrix.toLin'_apply,
    qLeftMat_mulVec, qLeftMat_mulVec, Matrix.smul_mul, map_smul]

theorem qLamMat_eq_qLeftMat (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) (g : SL(2, K)) :
    qLamMat h2 ha g = qLeftMat h2 ha g := by
  refine (Matrix.toLin' (R := K)).injective (LinearMap.ext fun x => ?_)
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, qLamMat_mulVec, qLeftMat_mulVec]

theorem qLeftMat_conj (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) (P : GL (Fin 2) K) (g : SL(2, K)) :
    qLeftMat h2 ha P * qLamMat h2 ha g * qLeftMat h2 ha ((P⁻¹ : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = qLamMat h2 ha (conjSL P g) := by
  rw [qLamMat_eq_qLeftMat, qLamMat_eq_qLeftMat, coe_conjSL, qLeftMat_mul, qLeftMat_mul]

theorem conj_oSlice_of_left (h2 : (2 : K) ≠ 0) (hd : 4 ≤ d) {a : K} (ha : a ≠ 0)
    {h : GL (Fin d) K}
    (hc : (h : Matrix (Fin d) (Fin d) K) * embed4 K hd (-1) =
      embed4 K hd (-1) * (h : Matrix (Fin d) (Fin d) K))
    {P : GL (Fin 2) K} (hP : blk4 hd (h : Matrix (Fin d) (Fin d) K) = qLeftMat h2 ha P)
    (g : SL(2, K)) : h * oSlice K h2 hd ha g * h⁻¹ = oSlice K h2 hd ha (conjSL P g) := by
  have hhi : (h : Matrix (Fin d) (Fin d) K) * ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hih : ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * (h : Matrix (Fin d) (Fin d) K) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hci : ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * embed4 K hd (-1) =
      embed4 K hd (-1) * ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
    commute_inv_of_commute hhi hih hc
  obtain ⟨e1, e2⟩ := mul_embed4_mul h2 hd hhi hc hci (qLamMat h2 ha g)
  have hPi : blk4 hd ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      qLeftMat h2 ha ((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    have hPP : qLeftMat h2 ha ((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        qLeftMat h2 ha P = 1 := by
      rw [← qLeftMat_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, qLeftMat_one]
    calc blk4 hd ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        (qLeftMat h2 ha ((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * qLeftMat h2 ha P) *
          blk4 hd ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by rw [hPP, Matrix.one_mul]
      _ = qLeftMat h2 ha ((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
        rw [Matrix.mul_assoc, ← hP, e2, Matrix.mul_one]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_oSlice, coe_oSlice, e1, hP, hPi, qLeftMat_conj]

theorem blk4_blkDiag_jMat (h2 : (2 : K) ≠ 0) {n : ℕ} (hn : 2 ≤ n) {c : K} (hc : c ≠ 0) :
    blk4 (by omega : 4 ≤ 2 * n) (blkDiag n (jMat c)) =
      qLeftMat h2 (neg_ne_zero.2 hc) (qXGL (neg_ne_zero.2 hc)) := by
  have hcol : ∀ k : Fin 4, qLeftMat h2 (neg_ne_zero.2 hc) (qXGL (neg_ne_zero.2 hc)) *ᵥ
      Pi.single k 1 = blk4 (by omega : 4 ≤ 2 * n) (blkDiag n (jMat c)) *ᵥ Pi.single k 1 := by
    intro k
    rw [qLeftMat_mulVec, coe_qXGL]
    funext i
    have hblk : ∀ i j : Fin 4, blk4 (by omega : 4 ≤ 2 * n) (blkDiag n (jMat c)) i j =
        !![(0 : K), c, 0, 0; 1, 0, 0, 0; 0, 0, 0, c; 0, 0, 1, 0] i j := by
      intro i j
      rw [blk4_apply]
      have hp : ∀ x : Fin 4, (⟨x, by omega⟩ : Fin (2 * n)) =
          pairEquiv n (⟨x / 2, by omega⟩, ⟨x % 2, by omega⟩) := by
        intro x
        apply Fin.ext
        rw [pairEquiv_val]
        simp only
        omega
      rw [hp i, hp j, blkDiag_apply]
      fin_cases i <;> fin_cases j <;> simp [jMat]
    simp only [mulVec, dotProduct, hblk]
    fin_cases k <;> fin_cases i <;>
      simp [qMat, qVec, Fin.sum_univ_four, qEquiv] <;> field_simp <;> first | ring1 | simp
  ext i j
  have := congrFun (hcol j) i
  simp only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at this
  exact this.symm

end CFSG.ComponentClassification.Burgoyne.O
