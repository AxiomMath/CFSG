module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSliceGen
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOPcLeft
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOPcCore

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat mul_conj_mul_inv)
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem kronI_mul_blkDiag (n : ℕ) (X : Matrix (Fin n) (Fin n) K)
    (W : Matrix (Fin 2) (Fin 2) K) : kronI K n X * blkDiag n W = blkDiag n W * kronI K n X := by
  rw [resMat_eq, blkDiag, ← map_mul, ← map_mul]
  congr 1
  ext i k : 1
  rw [mul_diagonal, diagonal_mul]
  simp only [map_apply]
  exact Algebra.commutes _ _

theorem wSet_eq_pairSet {n : ℕ} (hn : 2 ≤ n) :
    (wSet : Finset (Fin (2 * n))) = pairSet ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin n)) := by
  ext p
  obtain ⟨⟨i, j⟩, rfl⟩ := (pairEquiv n).surjective p
  rw [mem_wSet, mem_pairSet, pairEquiv_val]
  simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  have := j.2
  omega

theorem blkDiag_commute_embed4 {n : ℕ} (hn : 2 ≤ n) (W : Matrix (Fin 2) (Fin 2) K) :
    blkDiag n W * embed4 K (by omega : 4 ≤ 2 * n) (-1) =
      embed4 K (by omega : 4 ≤ 2 * n) (-1) * blkDiag n W := by
  rw [embed4_neg_one, wSet_eq_pairSet hn, ← kronI_signMat, kronI_mul_blkDiag]

theorem blk4_add {d : ℕ} (hd : 4 ≤ d) (M N : Matrix (Fin d) (Fin d) K) :
    blk4 hd (M + N) = blk4 hd M + blk4 hd N := by
  ext i j
  simp only [blk4_apply, Matrix.add_apply]

theorem blk4_smul {d : ℕ} (hd : 4 ≤ d) (r : K) (M : Matrix (Fin d) (Fin d) K) :
    blk4 hd (r • M) = r • blk4 hd M := by
  ext i j
  simp only [blk4_apply, Matrix.smul_apply]

theorem blk4_one {d : ℕ} (hd : 4 ≤ d) : blk4 hd (1 : Matrix (Fin d) (Fin d) K) = 1 := by
  ext i j
  rw [blk4_apply, one_apply, one_apply]
  simp only [Fin.mk.injEq, Fin.val_inj]

theorem kappa_conj_oSlice [Finite K] (h2 : (2 : K) ≠ 0) (hK4 : 4 ≤ Nat.card K) {d : ℕ}
    (hd : 4 ≤ d) {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {α a : K} (hW : OSliceW hd w α a)
    {g : similarityPairs (oQ (diagGL hw))} (hg : g.val.right = 1)
    (hc : (g.val.left : Matrix (Fin d) (Fin d) K) * embed4 K hd (-1) =
      embed4 K hd (-1) * (g.val.left : Matrix (Fin d) (Fin d) K))
    {P : GL (Fin 2) K} (hP : blk4 hd (g.val.left : Matrix (Fin d) (Fin d) K) = qLeftMat h2 hW.ha P)
    (x : SL(2, K)) :
    oκ _ g * conjProjH (matrixDerived (oQ (diagGL hw))) (oSliceH h2 hK4 hd hw hW x) * (oκ _ g)⁻¹ =
      conjProjH (matrixDerived (oQ (diagGL hw))) (oSliceH h2 hK4 hd hw hW (conjSL P x)) := by
  rw [MonoidHom.comp_apply, mul_conj_mul_inv, kappa_lift]
  change MulAut.conj (projH _ _) = MulAut.conj (projH _ _)
  congr 2
  apply Subtype.ext
  rw [MulEquiv.coe_toMonoidHom, matrixDerivedConjugation_val, hg, map_one, MulAut.one_apply]
  exact conj_oSlice_of_left h2 hd hW.ha hc hP x

variable [Finite K]

theorem slice_pc_propAConclusionIn (hK : ringChar K ≠ 2) (hK5 : 5 ≤ Nat.card K) {n : ℕ}
    (hn : 3 ≤ n) {c : K} (hc : c ≠ 0) {w : Fin (2 * n) → K} (hw : ∀ i, w i ≠ 0)
    (hW : OSliceW (by omega : 4 ≤ 2 * n) w 1 (-c)) (hker : OKer (oQ (diagGL hw)))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))))
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    (hB : (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))).range ≤ B)
    {g : similarityPairs (oQ (diagGL hw))} (hg1 : g.val.right = 1)
    (hgA : (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (jMat c))
    (hcore : ∀ y ∈ oddCoreIn B (oκ _ g), ∃ g' : similarityPairs (oQ (diagGL hw)),
      y = oκ _ g' ∧ g'.val.right = 1 ∧ ∃ x z : K,
        (g'.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = x • 1 + z • blkDiag n (jMat c))
    {Y : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))} (hY : Y ≠ ⊥)
    (hYO : Y ≤ oddCoreIn B (oκ _ g)) : PropAConclusionIn B (oκ _ g) Y := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hd4 : 4 ≤ 2 * n := by omega
  have hK4 : 4 ≤ Nat.card K := by omega
  set A := blkDiag n (jMat c) with hA
  have hA2 : A * A = c • 1 := by rw [hA, blkDiag_mul, jMat_mul_self, blkDiag_smul, blkDiag_one']
  have hAc : A * embed4 K hd4 (-1) = embed4 K hd4 (-1) * A := blkDiag_commute_embed4 (by omega) _
  have hAblk : blk4 hd4 A = qLeftMat h2 hW.ha (qXGL hW.ha) := blk4_blkDiag_jMat h2 (by omega) hc
  have hp00 : (pairEquiv n (⟨0, by omega⟩, 0)) ≠ pairEquiv n (⟨0, by omega⟩, 1) := by
    simp
  have hA01 : A (pairEquiv n (⟨0, by omega⟩, 0)) (pairEquiv n (⟨0, by omega⟩, 1)) = c := by
    simp only [hA, blkDiag_apply, ↓reduceIte]
    rfl
  have hA00 : A (pairEquiv n (⟨0, by omega⟩, 0)) (pairEquiv n (⟨0, by omega⟩, 0)) = 0 := by
    simp only [hA, blkDiag_apply, ↓reduceIte]
    rfl
  have ht : orderOf (oκ _ g) = 2 := by
    refine orderOf_eq_prime (kappa_pow_eq_one_of_pow hg1 (μ := Units.mk0 c hc) (by
      rw [hgA, pow_two, hA2]; rfl)) fun h1 => ?_
    obtain ⟨-, a, ha⟩ := hker _ h1
    have e := congrArg (fun M : GL (Fin (2 * n)) K => (M : Matrix (Fin (2 * n)) (Fin (2 * n)) K)
      (pairEquiv n (⟨0, by omega⟩, 0)) (pairEquiv n (⟨0, by omega⟩, 1))) ha
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_ne _ hp00] at e
    rw [hgA, hA01] at e
    exact hc e.symm
  refine slice_conj_propAConclusionIn hK hK5 (by omega) hw hW hinj hB ht (Pt := qXGL hW.ha)
    (fun x => kappa_conj_oSlice h2 hK4 hd4 hw hW hg1 (by rw [hgA]; exact hAc)
      (by rw [hgA]; exact hAblk) x) (conjSL_qX_ne hW.ha) (fun y hy => ?_) hY hYO
  obtain ⟨g', rfl, hg'1, x, z, hxz⟩ := hcore y hy
  set D := (g'.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) with hD
  have hDinv' : ((g'.val.left⁻¹ : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *
      D = 1 := by rw [hD, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hprod : D * (x • 1 - z • A) = (x ^ 2 - c * z ^ 2) • (1 : Matrix _ _ K) := by
    rw [hxz]
    simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, hA2]
    module
  have hδ : x ^ 2 - c * z ^ 2 ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hprod
    have h0' : x • (1 : Matrix (Fin (2 * n)) (Fin (2 * n)) K) - z • A = 0 := by
      have := congrArg (fun M => ((g'.val.left⁻¹ : GL (Fin (2 * n)) K) :
        Matrix (Fin (2 * n)) (Fin (2 * n)) K) * M) hprod
      simpa only [← Matrix.mul_assoc, hDinv', Matrix.one_mul, Matrix.mul_zero] using this
    have e0 := congrFun (congrFun h0' (pairEquiv n (⟨0, by omega⟩, 0)))
      (pairEquiv n (⟨0, by omega⟩, 0))
    have e1 := congrFun (congrFun h0' (pairEquiv n (⟨0, by omega⟩, 0)))
      (pairEquiv n (⟨0, by omega⟩, 1))
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, hA00, one_apply_eq] at e0
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, hA01, one_apply_ne hp00] at e1
    simp only [smul_eq_mul, mul_one, mul_zero, sub_zero, Matrix.zero_apply, zero_sub,
      neg_eq_zero] at e0 e1
    have hz0 : z = 0 := (mul_eq_zero.1 e1).resolve_right hc
    have hD0 : D = 0 := by rw [hxz, e0, hz0, zero_smul, zero_smul, add_zero]
    rw [hD0, Matrix.mul_zero] at hDinv'
    have := congrFun (congrFun hDinv' (pairEquiv n (⟨0, by omega⟩, 0)))
      (pairEquiv n (⟨0, by omega⟩, 0))
    simp at this
  set X₀ : Matrix (Fin 2) (Fin 2) K := ((qXGL hW.ha : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
    with hX₀
  have hX₀2 : X₀ * X₀ = c • 1 := by
    rw [hX₀, coe_qXGL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hPP0 : (x • 1 + z • X₀) * (x • 1 - z • X₀) = (x ^ 2 - c * z ^ 2) • 1 := by
    simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, hX₀2]
    module
  have hPP1 : (x • 1 - z • X₀) * (x • 1 + z • X₀) = (x ^ 2 - c * z ^ 2) • 1 := by
    simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, hX₀2]
    module
  have hPP : (x • 1 + z • X₀) * ((x ^ 2 - c * z ^ 2)⁻¹ • (x • 1 - z • X₀)) = 1 := by
    rw [Matrix.mul_smul, hPP0, smul_smul, inv_mul_cancel₀ hδ, one_smul]
  have hPP' : ((x ^ 2 - c * z ^ 2)⁻¹ • (x • 1 - z • X₀)) * (x • 1 + z • X₀) = 1 := by
    rw [Matrix.smul_mul, hPP1, smul_smul, inv_mul_cancel₀ hδ, one_smul]
  let P : GL (Fin 2) K := ⟨x • 1 + z • X₀, (x ^ 2 - c * z ^ 2)⁻¹ • (x • 1 - z • X₀), hPP, hPP'⟩
  have hDc : D * embed4 K hd4 (-1) = embed4 K hd4 (-1) * D := by
    rw [hxz]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, hAc]
  have hDP : blk4 hd4 D = qLeftMat h2 hW.ha P := by
    rw [hxz, blk4_add, blk4_smul, blk4_smul, blk4_one, hAblk]
    change _ = qLeftMat h2 hW.ha (x • 1 + z • X₀)
    rw [qLeftMat_add, qLeftMat_smul, qLeftMat_smul, qLeftMat_one]
  refine ⟨P, fun x' => kappa_conj_oSlice h2 hK4 hd4 hw hW hg'1 hDc hDP x', ?_⟩
  rintro ⟨c', hc'⟩
  have e := congrArg (fun M : GL (Fin 2) K => (M : Matrix (Fin 2) (Fin 2) K) 1 0) hc'
  simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    diagonal_apply_ne _ (by decide : (1 : Fin 2) ≠ 0)] at e
  change (x • (1 : Matrix (Fin 2) (Fin 2) K) + z • X₀) 1 0 = 0 at e
  rw [hX₀, coe_qXGL] at e
  simp only [Matrix.add_apply, Matrix.smul_apply, one_apply_ne (by decide : (1 : Fin 2) ≠ 0),
    smul_eq_mul, mul_zero, zero_add, of_apply, cons_val', cons_val_zero, cons_val_one,
    empty_val', cons_val_fin_one, mul_neg, mul_one, neg_eq_zero] at e
  have hx0 : x ≠ 0 := by
    intro h
    apply hδ
    rw [h, e]
    ring
  refine (oκ_eq_of_left_eq (g' := 1) (c := Units.mk0 x hx0) (by rw [hg'1]; rfl) ?_).trans
    (map_one _)
  apply Units.ext
  rw [Units.val_mul, GeneralLinearGroup.coe_scalar]
  change D = Matrix.scalar _ x * 1
  rw [hxz, e, zero_smul, add_zero, Matrix.mul_one, Matrix.scalar_apply, smul_one_eq_diagonal]

end CFSG.ComponentClassification.Burgoyne.O
