module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXKlComp
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOKronElts
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOPc
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOType

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX.Kl

open Module Matrix CFSG Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (signMat signMat_mul_self reflGL rotGL)
open scoped commutatorElement

variable {K : Type} [Field K]

theorem signMat_pairSet_spec (h2 : (2 : K) ≠ 0) {n : ℕ} {i j k : Fin n} (hki : k ≠ i)
    (hkj : k ≠ j) {u : GL (Fin (2 * n)) K}
    (hu : (u : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = signMat K (pairSet {i, j})) :
    u * u = 1 ∧ u ≠ 1 ∧ u ≠ -1 := by
  have hi : pairEquiv n (i, 0) ∈ pairSet {i, j} := (mem_pairSet _ _ _).2 (by simp)
  have hk : pairEquiv n (k, 0) ∉ pairSet {i, j} := by
    rw [mem_pairSet]
    simp [hki, hkj]
  refine ⟨Units.ext (by rw [Units.val_mul, hu, signMat_mul_self, Units.val_one]), ?_, ?_⟩
  · intro h
    have e := congrArg (fun B : GL (Fin (2 * n)) K =>
      (B : Matrix (Fin (2 * n)) (Fin (2 * n)) K) (pairEquiv n (i, 0)) (pairEquiv n (i, 0))) h
    simp only [hu, signMat, diagonal_apply_eq, hi, ↓reduceIte, Units.val_one,
      one_apply_eq] at e
    exact h2 (by linear_combination -e)
  · intro h
    have e := congrArg (fun B : GL (Fin (2 * n)) K =>
      (B : Matrix (Fin (2 * n)) (Fin (2 * n)) K) (pairEquiv n (k, 0)) (pairEquiv n (k, 0))) h
    simp only [hu, signMat, diagonal_apply_eq, hk, ↓reduceIte, Units.val_neg, Units.val_one,
      Matrix.neg_apply, one_apply_eq] at e
    exact h2 (by linear_combination e)

variable [Finite K]

theorem false_of_k2_pc (hK : ringChar K ≠ 2) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hKc : Nat.card K = ℓ ^ f)
    {c : K} (hc : c ≠ 0) {n : ℕ} (hn : 3 ≤ n) {R : GL (Fin (2 * n)) K}
    (hRm : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (wMat 1 (-c)))
    {M : Subgroup (GL (Fin (2 * n)) K)} (hd : K2Data R M) {gs : similarityPairs (oQ R)}
    (hσ : gs.val.right = 1)
    (hgA : (gs.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (jMat c))
    (hQs : (M.subgroupOf (matrixDerived (oQ R))).map (projH _) ≤ autFixed (oκ _ gs))
    (hQc : IsPComponent 2 (((M.subgroupOf (matrixDerived (oQ R))).map (projH _)).subgroupOf
      (autFixed (oκ _ gs)))) : False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hRs : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R := by
    rw [hRm, blkDiag_transpose, wMat, diagonal_transpose]
  have hN := C.isQuasisimple_isoCent_pc hK hℓ hKc hc hn hRm hgA
  set i₀ : Fin n := ⟨0, by omega⟩ with hi₀
  set j₀ : Fin n := ⟨1, by omega⟩ with hj₀
  set k₀ : Fin n := ⟨2, by omega⟩ with hk₀
  have hij : i₀ ≠ j₀ := by simp [hi₀, hj₀, Fin.ext_iff]
  have h01 : (0 : K) ^ 2 + (1 : K) ^ 2 = 1 := by ring
  have hu : kronGL K n ⁅reflGL (K := K) i₀, rotGL i₀ j₀ hij h01⁆ ∈
      (⁅isoCent R gs.val.left, isoCent R gs.val.left⁆ : Subgroup (GL (Fin (2 * n)) K)) := by
    rw [map_commutatorElement]
    exact commutator_mem_commutator (kronGL_mem_isoCent_blkDiag hRm hgA (reflGL_orth i₀))
      (kronGL_mem_isoCent_blkDiag hRm hgA (rotGL_orth hij h01))
  have huv : ((kronGL K n ⁅reflGL (K := K) i₀, rotGL i₀ j₀ hij h01⁆ : GL (Fin (2 * n)) K) :
      Matrix (Fin (2 * n)) (Fin (2 * n)) K) = signMat K (pairSet {i₀, j₀}) := by
    rw [coe_kronGL, signMat_pair_eq_commutator hij h01, kronI_signMat]
  obtain ⟨huu, hu1, hun⟩ := signMat_pairSet_spec h2 (k := k₀)
    (by simp [hi₀, hk₀, Fin.ext_iff]) (by simp [hj₀, hk₀, Fin.ext_iff]) huv
  exact false_of_k2_isoCent hK hRs hd hσ hQs hQc (Or.inr hN) hu huu hu1 hun

end CFSG.ComponentClassification.Burgoyne.DX.Kl
