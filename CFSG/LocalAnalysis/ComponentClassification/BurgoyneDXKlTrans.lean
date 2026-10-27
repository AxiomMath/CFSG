module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXKlOrth2
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXExcTrans
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEvenModel
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSliceNF
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSplitCases

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX.Kl

open Module Matrix CFSG Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL exists_frame)

variable {K : Type} [Field K] [Finite K]

theorem false_of_k2_skew (hK : ringChar K ≠ 2) {ℓ e : ℕ} (hℓ : ℓ.Prime) (hKc : Nat.card K = ℓ ^ e)
    {n : ℕ} (hn : 3 ≤ n) {R : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R)
    {M : Subgroup (GL (Fin (2 * n)) K)} (hd : K2Data R M) {gs : similarityPairs (oQ R)}
    (hσ : gs.val.right = 1) {c : K} (hc : c ≠ 0)
    (hS2 : (gs.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * gs.val.left = c • 1)
    (hSR : (gs.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ * R =
      (-1 : K) • ((R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * gs.val.left))
    (hQs : (M.subgroupOf (matrixDerived (oQ R))).map (projH _) ≤ autFixed (oκ _ gs))
    (hQc : IsPComponent 2 (((M.subgroupOf (matrixDerived (oQ R))).map (projH _)).subgroupOf
      (autFixed (oκ _ gs)))) : False := by
  obtain ⟨H₁, hgram₁, hAH₁⟩ := exists_pc_basis hK hR hc hS2 hSR (fun _ => 1)
    (fun _ => one_ne_zero)
  obtain ⟨R₁, hR₁⟩ : ∃ R₁, R₁ = CatalogueBGraphForm.glTranspose (2 * n) K H₁ * R * H₁ :=
    ⟨_, rfl⟩
  have hgramR₁ : (H₁ : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ * R * H₁ = R₁ := by
    rw [hR₁]
    simp only [Units.val_mul, CatalogueBGraphForm.glTranspose_matrix]
  have hR₁m : (R₁ : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (wMat 1 (-c)) := by
    rw [← hgramR₁, hgram₁]
    simp only [one_smul]
    rfl
  obtain ⟨hS, hl, hr⟩ := exists_transport_of_gram hgramR₁ hσ
  have hd' := hd.transport H₁⁻¹ 1 hS
  obtain ⟨hQs', hQc'⟩ := transport_comp hd.le H₁⁻¹ 1 hS hQs hQc
  have hgA : ((transPair H₁⁻¹ 1 hS gs).val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
      blkDiag n (jMat c) := by
    rw [hl, Units.val_mul, Units.val_mul]
    exact inv_mul_mul_eq hAH₁
  exact false_of_k2_pc hK hℓ hKc hc hn hR₁m hd' hr hgA hQs' hQc'

theorem false_of_k2_nonsq (hK : ringChar K ≠ 2) {n : ℕ} (hn : 5 ≤ n) {R : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R)
    {M : Subgroup (GL (Fin (2 * n)) K)} (hd : K2Data R M) {gs : similarityPairs (oQ R)}
    (hσ : gs.val.right = 1) {c : K} (hc : ¬ IsSquare c)
    (hS2 : (gs.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * gs.val.left = c • 1)
    (hSR : (gs.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ * R =
      (1 : K) • ((R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * gs.val.left))
    (hQs : (M.subgroupOf (matrixDerived (oQ R))).map (projH _) ≤ autFixed (oκ _ gs))
    (hQc : IsPComponent 2 (((M.subgroupOf (matrixDerived (oQ R))).map (projH _)).subgroupOf
      (autFixed (oκ _ gs)))) : False := by
  have hc0 : c ≠ 0 := fun h => hc ⟨0, by rw [h, mul_zero]⟩
  have : Fact (Irreducible (sqPoly c)) := ⟨irreducible_sqPoly hc⟩
  obtain ⟨H, β, hβ0, hgram, hAH⟩ := exists_orth2_basis hK hR hc hS2 hSR
  obtain ⟨hEf, hE⟩ := finite_ringChar_EAlg hK hc0
  obtain ⟨P, w, hw, hw1, hP⟩ := exists_frame hE (by omega : 2 ≤ n) (diagGL hβ0)
    (by rw [coe_diagGL]; exact diagonal_transpose _) (one_ne_zero (α := EAlg c))
  rw [coe_diagGL] at hP
  obtain ⟨Sr, hSr⟩ : ∃ S, S = resGL (phiE c).toRingHom n P := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = H * Sr := ⟨_, rfl⟩
  obtain ⟨R₂, hR₂⟩ : ∃ R₂, R₂ = CatalogueBGraphForm.glTranspose (2 * n) K G * R * G := ⟨_, rfl⟩
  have hW : ∀ x, ((phiE c).toRingHom x)ᵀ * wMat 1 c = wMat 1 c * (phiE c).toRingHom
      (RingHom.id _ x) := fun x => transpose_phiE_mul_wOne hc0 x
  have hPid : (P : Matrix (Fin n) (Fin n) (EAlg c)).map (RingHom.id _) = P := by
    ext
    rfl
  have hR₂m : (R₂ : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
      blkDiag n (wMat 1 c) * resMat (phiE c).toRingHom n (diagonal w) := by
    rw [hR₂, Units.val_mul, Units.val_mul, CatalogueBGraphForm.glTranspose_matrix, hG,
      Units.val_mul, transpose_mul, hSr]
    change (resMat (phiE c).toRingHom n (P : Matrix (Fin n) (Fin n) (EAlg c)))ᵀ *
        (H : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ * R *
          ((H : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *
            resMat (phiE c).toRingHom n (P : Matrix (Fin n) (Fin n) (EAlg c))) = _
    rw [show (resMat (phiE c).toRingHom n (P : Matrix (Fin n) (Fin n) (EAlg c)))ᵀ *
        (H : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ * R *
          ((H : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *
            resMat (phiE c).toRingHom n (P : Matrix (Fin n) (Fin n) (EAlg c))) =
        (resMat (phiE c).toRingHom n (P : Matrix (Fin n) (Fin n) (EAlg c)))ᵀ *
          ((H : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ * R * H) *
            resMat (phiE c).toRingHom n (P : Matrix (Fin n) (Fin n) (EAlg c)) by
      simp only [Matrix.mul_assoc], hgram, resMat_transpose_mul_mul hW, hPid, hP]
  have hgram₂ : (G : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ * R * G = R₂ := by
    rw [hR₂]
    simp only [Units.val_mul, CatalogueBGraphForm.glTranspose_matrix]
  obtain ⟨hS, hl, hr⟩ := exists_transport_of_gram hgram₂ hσ
  have hd' := hd.transport G⁻¹ 1 hS
  obtain ⟨hQs', hQc'⟩ := transport_comp hd.le G⁻¹ 1 hS hQs hQc
  have hSA : (Sr : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * blkDiag n (jMat c) =
      blkDiag n (jMat c) * Sr := by
    have hj : jMat c = (phiE c).toRingHom (AdjoinRoot.root (sqPoly c)) := (phiE_root c).symm
    rw [hSr, coe_resGL, hj, ← resMat_diagonal, ← map_mul, ← map_mul]
    congr 1
    ext i k
    rw [mul_diagonal, diagonal_mul, mul_comm]
  have hgA : ((transPair G⁻¹ 1 hS gs).val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
      blkDiag n (jMat c) := by
    rw [hl, hG, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul]
    have e1 := inv_mul_mul_eq hAH
    have e2 := inv_mul_mul_eq hSA.symm
    calc ((Sr⁻¹ : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *
          ((H⁻¹ : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *
          (gs.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *
          ((H : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * Sr) =
        ((Sr⁻¹ : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *
          (((H⁻¹ : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *
            (gs.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * H) * Sr := by
          simp only [Matrix.mul_assoc]
      _ = blkDiag n (jMat c) := by rw [e1, e2]
  have hR₂s : (R₂ : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R₂ := by
    rw [← hgram₂, transpose_mul, transpose_mul, transpose_transpose, hR, Matrix.mul_assoc]
  exact false_of_k2_orth2 hK hc hn hw hw1 hR₂s hR₂m hd' hr hgA hQs' hQc'

end CFSG.ComponentClassification.Burgoyne.DX.Kl
