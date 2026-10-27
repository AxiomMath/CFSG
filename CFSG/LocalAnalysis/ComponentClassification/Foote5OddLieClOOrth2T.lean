module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClOOrth2
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClOOddInner
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEvenOrth2

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL exists_frame)

variable {K : Type} [Field K] [Finite K]

theorem ClO.commute_orth2 (hK : ringChar K ≠ 2) {n : ℕ} (hn : 4 ≤ n)
    {R : GL (Fin (2 * n)) K} (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R)
    (hker : OKer (oQ R)) (hsurj : OSurj (oQ R))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ R)) →*
      MulAut (StatedProj (matrixDerived (oQ R)))))
    {g : similarityPairs (oQ R)} (hg1 : g.val.right = 1) {c : K} (hc : ¬ IsSquare c)
    (hA2 : (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * g.val.left = c • 1)
    (hAR : (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ * R =
      (1 : K) • ((R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * g.val.left))
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ R))))} (hRodd : Odd (Nat.card Ro))
    (hRi : ∀ y ∈ Ro, y * oκ _ g = oκ _ g * y)
    (hRc : ∀ s, oκ _ g s = s → Odd (orderOf s) → ∀ y ∈ Ro,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ Ro) :
    ∀ r₁ ∈ Ro, ∀ r₂ ∈ Ro, r₁ * r₂ = r₂ * r₁ := by
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
  obtain ⟨hS', hg'l, hg'1⟩ := exists_transport_of_gram hgram₂ hg1
  have hSA : (S : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * blkDiag n (jMat c) =
      blkDiag n (jMat c) * S := by
    have hj : jMat c = (phiE c).toRingHom (AdjoinRoot.root (sqPoly c)) := (phiE_root c).symm
    rw [hS, coe_resGL, hj, ← resMat_diagonal, ← map_mul, ← map_mul]
    congr 1
    ext i k
    rw [mul_diagonal, diagonal_mul, mul_comm]
  have hg'A : ((transPair M⁻¹ 1 hS' g).val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
      blkDiag n (jMat c) := by
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
  refine commute_of_congr (oTransport M⁻¹ 1 hS') (fun R' hR'odd hR'i hR'c => ?_) hRodd hRi hRc
  rw [oTransport_kappa] at hR'i hR'c
  have h1 := ClO.orth2_eq_one hK hc hn hw hw1 hR₂s hR₂m (hker.transport M⁻¹ 1 hS')
    (ClO.conj_injective_of_mulEquiv (oTransport M⁻¹ 1 hS') hinj) hg'1 hg'A hR'odd hR'i hR'c
    (fun y _ => (hsurj.transport M⁻¹ 1 hS') y)
  intro r₁ h₁ r₂ h₂
  rw [h1 r₁ h₁, h1 r₂ h₂]

end CFSG.ComponentClassification.Foote5.OddLieCore
