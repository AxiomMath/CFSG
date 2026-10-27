module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEvenOrth2
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10OrthCent

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.X10Orth

open Module Matrix CFSG Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (signMat diagGL coe_diagGL reflGL rotGL
  rotMat_apply_ne_zero exists_frame)
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem kron_signPair_mem_orth2 {c : K} (hc0 : c ≠ 0) [Fact (Irreducible (sqPoly c))] {n : ℕ}
    {w : Fin n → EAlg c} {R A : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
      blkDiag n (wMat 1 c) * resMat (phiE c).toRingHom n (diagonal w))
    (hgA : (A : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (jMat c)) {i j : Fin n}
    (hij : i ≠ j) (hwij : w i = w j) :
    signGL K (pairSet {i, j}) ∈ (⁅isoCent R A, isoCent R A⁆ : Subgroup (GL (Fin (2 * n)) K)) := by
  have hφa : ∀ a : K, (phiE c).toRingHom (algebraMap K (EAlg c) a) =
      algebraMap K (Matrix (Fin 2) (Fin 2) K) a := phiE_algebraMap c
  have hkron : ∀ X : GL (Fin n) K, (X : Matrix (Fin n) (Fin n) K)ᵀ * X = 1 →
      (∀ x y, (X : Matrix (Fin n) (Fin n) K) x y ≠ 0 → w x = w y) →
      kronGL K n X ∈ isoCent R A := fun X hX hXw =>
    kronGL_mem_iso_inf (σ := RingHom.id (EAlg c)) hφa (fun _ => rfl)
      (fun x => transpose_phiE_mul_wOne hc0 x) (phiE_root c) hR hgA hX (map_mul_diagonal_comm hXw)
  have h01 : (0 : K) ^ 2 + (1 : K) ^ 2 = 1 := by ring
  have hrefl : kronGL K n (reflGL i) ∈ isoCent R A :=
    hkron _ (reflGL_orth i) fun x y h => by rw [reflGL_support i h]
  have hrot : kronGL K n (rotGL i j hij h01) ∈ isoCent R A := by
    refine hkron _ (rotGL_orth hij h01) fun x y h => ?_
    by_cases hxy : x = y
    · rw [hxy]
    rcases rotMat_apply_ne_zero hxy h with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · rw [hx, hy, hwij]
    · rw [hx, hy, hwij]
  have e : kronGL K n ⁅reflGL (K := K) i, rotGL i j hij h01⁆ = signGL K (pairSet {i, j}) :=
    Units.ext (by rw [coe_kronGL, signMat_pair_eq_commutator hij h01, kronI_signMat,
      coe_signGL])
  rw [← e, map_commutatorElement]
  exact commutator_mem_commutator hrefl hrot

theorem false_of_orth2_five (hK : ringChar K ≠ 2) {c : K} (hc : ¬ IsSquare c) {n : ℕ}
    (hn : 5 ≤ n) [Fact (Irreducible (sqPoly c))] {w : Fin n → EAlg c} (hw : ∀ i, w i ≠ 0)
    (hw1 : ∀ i : Fin n, (i : ℕ) + 1 < n → w i = 1) {R : GL (Fin (2 * n)) K}
    (hRs : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R)
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
      blkDiag n (wMat 1 c) * resMat (phiE c).toRingHom n (diagonal w))
    {gs : similarityPairs (oQ R)} (hσ : gs.val.right = 1)
    (hgA : (gs.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (jMat c))
    {M : Subgroup (GL (Fin (2 * n)) K)} {Q : ℕ} (h : X10Data R gs M Q) : False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hc0 : c ≠ 0 := fun h => hc ⟨0, by rw [h, mul_zero]⟩
  have hZ := commutator_iso_inf_centralizer_eq (φ := (phiE c).toRingHom)
    (σ := RingHom.id (EAlg c)) (r := AdjoinRoot.root (sqPoly c)) (phiE_injective c)
    (wOne_inv_mul hc0) (fun x => transpose_phiE_mul_wOne hc0 x) (phiE_root c)
    (fun M hM => phiE_mem_range hc0 hM) (diagonal w) hR hgA
  rw [uGrp_id_eq_iso hw] at hZ
  obtain ⟨hEf, hE⟩ := finite_ringChar_EAlg hK hc0
  have hinj := resGL_injective (phiE_injective c) n
  have hN : Group.IsSolvable (⁅isoCent R gs.val.left, isoCent R gs.val.left⁆ :
        Subgroup (GL (Fin (2 * n)) K)) ∨
      IsQuasisimple (⁅isoCent R gs.val.left, isoCent R gs.val.left⁆ :
        Subgroup (GL (Fin (2 * n)) K)) := by
    rw [hZ]
    rcases C.orth_block_cases hE (by omega : 3 ≤ n) (diagGL hw)
        (by rw [coe_diagGL]; exact diagonal_transpose _) with hsol | hqs | ⟨h4, -⟩
    · left
      exact Group.isSolvable_of_surjective
        (MonoidHom.subgroupMap_surjective (resGL (phiE c).toRingHom n) (C.omegaR (diagGL hw)))
    · right
      exact LocalCores.isQuasisimple_of_mulEquiv
        ((C.omegaR (diagGL hw)).equivMapOfInjective _ hinj) hqs
    · omega
  set i₀ : Fin n := ⟨0, by omega⟩
  set i₁ : Fin n := ⟨1, by omega⟩
  set i₂ : Fin n := ⟨2, by omega⟩
  set i₃ : Fin n := ⟨3, by omega⟩
  have hd : ∀ a b : Fin n, (a : ℕ) ≠ b → a ≠ b := fun a b hab h' => hab (by rw [h'])
  have h01 := hd i₀ i₁ (by simp [i₀, i₁])
  have h02 := hd i₀ i₂ (by simp [i₀, i₂])
  have h03 := hd i₀ i₃ (by simp [i₀, i₃])
  have h12 := hd i₁ i₂ (by simp [i₁, i₂])
  have h13 := hd i₁ i₃ (by simp [i₁, i₃])
  have h23 := hd i₂ i₃ (by simp [i₂, i₃])
  have hw0 : w i₀ = 1 := hw1 i₀ (by simp [i₀]; omega)
  have hw1' : w i₁ = 1 := hw1 i₁ (by simp [i₁]; omega)
  have hw2 : w i₂ = 1 := hw1 i₂ (by simp [i₂]; omega)
  have hw3 : w i₃ = 1 := hw1 i₃ (by simp [i₃]; omega)
  exact h.false_of_isoCent_e8 hK hRs hσ hN
    (kron_signPair_mem_orth2 hc0 hR hgA h01 (by rw [hw0, hw1']))
    (kron_signPair_mem_orth2 hc0 hR hgA h02 (by rw [hw0, hw2]))
    (kron_signPair_mem_orth2 hc0 hR hgA h03 (by rw [hw0, hw3]))
    fun hX hY hZ => e8Triple_kron_sign h2 hn h01 h02 h03 h12 h13 h23 hX hY hZ

theorem exists_orth2_model (hK : ringChar K ≠ 2) {n : ℕ} (hn : 2 ≤ n) {R : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R) (hker : OKer (oQ R))
    {gs : similarityPairs (oQ R)} (hσ : gs.val.right = 1) {c : K} (hc : ¬ IsSquare c)
    [Fact (Irreducible (sqPoly c))]
    (hS2 : (gs.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * gs.val.left = c • 1)
    (hSR : (gs.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ * R =
      (1 : K) • ((R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * gs.val.left))
    {M : Subgroup (GL (Fin (2 * n)) K)} {Q : ℕ} (h : X10Data R gs M Q) :
    ∃ w : Fin n → EAlg c, (∀ i, w i ≠ 0) ∧ (∀ i : Fin n, (i : ℕ) + 1 < n → w i = 1) ∧
      ∃ (R₂ : GL (Fin (2 * n)) K) (gs₂ : similarityPairs (oQ R₂))
        (M₂ : Subgroup (GL (Fin (2 * n)) K)),
        (R₂ : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R₂ ∧
        (R₂ : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
          blkDiag n (wMat 1 c) * resMat (phiE c).toRingHom n (diagonal w) ∧
        OKer (oQ R₂) ∧ gs₂.val.right = 1 ∧
        (gs₂.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (jMat c) ∧
        X10Data R₂ gs₂ M₂ Q ∧ (oκ _ gs₂ = 1 → oκ _ gs = 1) := by
  have hc0 : c ≠ 0 := fun h => hc ⟨0, by rw [h, mul_zero]⟩
  obtain ⟨H, β, hβ0, hgram, hAH⟩ := exists_orth2_basis hK hR hc hS2 hSR
  obtain ⟨hEf, hE⟩ := finite_ringChar_EAlg hK hc0
  obtain ⟨P, w, hw, hw1, hP⟩ := exists_frame hE hn (diagGL hβ0)
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
  refine ⟨w, hw, hw1, R₂, transPair G⁻¹ 1 hS gs, M.map (MulAut.conj G⁻¹).toMonoidHom, hR₂s,
    hR₂m, hker.transport G⁻¹ 1 hS, hr, hgA, h.transport G⁻¹ 1 hS, fun h1 => ?_⟩
  rw [← oTransport_kappa] at h1
  exact (MulAut.congr (oTransport G⁻¹ 1 hS)).injective (by rw [h1, map_one])

end CFSG.ComponentClassification.GSThmB.X10Orth
