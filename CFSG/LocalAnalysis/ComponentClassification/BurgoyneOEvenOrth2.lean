module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEvenModel
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOPairNorm
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOOrth2

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL exists_frame)

variable {K : Type} [Field K] [Finite K]

theorem finite_ringChar_EAlg (hK : ringChar K ≠ 2) {c : K} [Fact (Irreducible (sqPoly c))]
    (hc0 : c ≠ 0) : Finite (EAlg c) ∧ ringChar (EAlg c) ≠ 2 := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hchar, -⟩ := FiniteField.card' K
  have : CharP (EAlg c) p := charP_of_injective_algebraMap (algebraMap K (EAlg c)).injective p
  refine ⟨Nat.finite_of_card_ne_zero ?_, ?_⟩
  · rw [card_EAlg hc0]
    exact pow_ne_zero 2 Nat.card_pos.ne'
  · rw [ringChar.eq (EAlg c) p, ← ringChar.eq K p]
    exact hK

omit [Finite K] in
theorem inv_mul_mul_eq {d : ℕ} {H : GL (Fin d) K} {A A₁ : Matrix (Fin d) (Fin d) K}
    (h : A * H = H * A₁) : ((H⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * A * H = A₁ := by
  rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mul]

theorem orth2_oddCentralizerCore_eq_bot (hK : ringChar K ≠ 2) {n : ℕ} (hn : 4 ≤ n)
    {R : GL (Fin (2 * n)) K} (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R)
    (hker : OKer (oQ R)) {X : Type} [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (θ : GeneralizedFitting.subgroup X ≃* StatedProj (matrixDerived (oQ R)))
    {t : X} (hsurj : OSurjX θ t) {g : similarityPairs (oQ R)} (hg1 : g.val.right = 1)
    (htg : socleAction θ t = oκ _ g) {c : K} (hc : ¬ IsSquare c)
    (hA2 : (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * g.val.left = c • 1)
    (hAR : (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ * R =
      (1 : K) • ((R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * g.val.left)) :
    oddCentralizerCore t = ⊥ := by
  have hc0 : c ≠ 0 := fun h => hc ⟨0, by rw [h, mul_zero]⟩
  have : Fact (Irreducible (sqPoly c)) := ⟨irreducible_sqPoly hc⟩
  obtain ⟨H, β, hβ0, hgram, hAH⟩ := exists_orth2_basis hK hR hc hA2 hAR
  obtain ⟨hEf, hE⟩ := finite_ringChar_EAlg hK hc0
  obtain ⟨P, w, hw, hw1, hP⟩ := exists_frame hE (by omega : 2 ≤ n) (diagGL hβ0)
    (by rw [coe_diagGL]; exact diagonal_transpose _) (one_ne_zero (α := EAlg c))
  rw [coe_diagGL] at hP
  obtain ⟨S, hS⟩ : ∃ S, S = resGL (phiE c).toRingHom n P := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = H * S := ⟨_, rfl⟩
  obtain ⟨R₂, hR₂⟩ : ∃ R₂, R₂ = CatalogueBGraphForm.glTranspose (2 * n) K M * R * M := ⟨_, rfl⟩
  have hW : ∀ x, ((phiE c).toRingHom x)ᵀ * wMat 1 c = wMat 1 c * (phiE c).toRingHom
      (RingHom.id _ x) := fun x => transpose_phiE_mul_wOne hc0 x
  have hPid : (P : Matrix (Fin n) (Fin n) (EAlg c)).map (RingHom.id _) = P := by
    ext
    rfl
  have hR₂m : (R₂ : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
      blkDiag n (wMat 1 c) * resMat (phiE c).toRingHom n (diagonal w) := by
    rw [hR₂, Units.val_mul, Units.val_mul, CatalogueBGraphForm.glTranspose_matrix, hM,
      Units.val_mul, transpose_mul, hS]
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
  have hgram₂ : (M : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ * R * M = R₂ := by
    rw [hR₂]
    simp only [Units.val_mul, CatalogueBGraphForm.glTranspose_matrix]
  obtain ⟨θ', g', hg'1, hg'l, htg', hker', hsurj', -, hinj', hB'⟩ :=
    exists_model hker hsimple hnab θ hsurj hg1 htg hgram₂
  have hSA : (S : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * blkDiag n (jMat c) =
      blkDiag n (jMat c) * S := by
    have hj : jMat c = (phiE c).toRingHom (AdjoinRoot.root (sqPoly c)) := (phiE_root c).symm
    rw [hS, coe_resGL, hj, ← resMat_diagonal, ← map_mul, ← map_mul]
    congr 1
    ext i k
    rw [mul_diagonal, diagonal_mul, mul_comm]
  have hg'A : (g'.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (jMat c) := by
    rw [hg'l, hM, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul]
    have e1 := inv_mul_mul_eq hAH
    have e2 := inv_mul_mul_eq hSA.symm
    calc ((S⁻¹ : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *
          ((H⁻¹ : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *
          (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *
          ((H : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * S) =
        ((S⁻¹ : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *
          (((H⁻¹ : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *
            (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * H) * S := by
          simp only [Matrix.mul_assoc]
      _ = blkDiag n (jMat c) := by rw [e1, e2]
  have hR₂s : (R₂ : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R₂ := by
    rw [← hgram₂, transpose_mul, transpose_mul, transpose_transpose, hR, Matrix.mul_assoc]
  have hbot := orth2_oddCoreIn_eq_bot hK hc hn hw hw1 hR₂s hR₂m hker' hinj' hB' hg'1 hg'A
    ((hsurj'.core hsimple hnab).of_eq htg')
  have hψ' := socleAction_injective hsimple hnab θ'
  rw [← htg', ← map_oddCentralizerCore_of_injective hψ'] at hbot
  exact (map_eq_bot_iff_of_injective _ hψ').1 hbot

theorem orth2_propAConclusion (hK : ringChar K ≠ 2) {n : ℕ} (hn : 4 ≤ n)
    {R : GL (Fin (2 * n)) K} (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R)
    (hker : OKer (oQ R)) {X : Type} [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (θ : GeneralizedFitting.subgroup X ≃* StatedProj (matrixDerived (oQ R)))
    {t : X} (hsurj : OSurjX θ t) {g : similarityPairs (oQ R)} (hg1 : g.val.right = 1)
    (htg : socleAction θ t = oκ _ g) {c : K} (hc : ¬ IsSquare c)
    (hA2 : (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * g.val.left = c • 1)
    (hAR : (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ * R =
      (1 : K) • ((R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * g.val.left))
    {Y : Subgroup X} (hY : Y ≠ ⊥) (hYO : Y ≤ oddCentralizerCore t) : PropAConclusion X t Y := by
  have hbot := orth2_oddCentralizerCore_eq_bot hK hn hR hker hsimple hnab θ hsurj hg1 htg hc hA2
    hAR
  exact absurd (le_bot_iff.1 (hbot ▸ hYO)) hY

end CFSG.ComponentClassification.Burgoyne.O
