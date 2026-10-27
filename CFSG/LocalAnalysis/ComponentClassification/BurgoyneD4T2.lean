module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneD4Field
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneD4PcSq
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneD4Orth2
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneD4Disc
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneInputs
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEvenInner
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOFieldNF
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOFormEven
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOOddSlice
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataPlusImage
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LieType.Universal.SpinOmega.Kernel
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneD4Coord
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.D4

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation (sq_val)
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL exists_frame)

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem Sit.gram {d : ℕ} {R R' H : GL (Fin d) K}
    (hgram : (H : Matrix (Fin d) (Fin d) K)ᵀ * R * H = R')
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ R))))}
    {y : MulAut (StatedProj (matrixDerived (oQ R)))} {g : similarityPairs (oQ R)}
    (h : Sit (oQ R) B (oκ _ g) y) (hg1 : g.val.right = 1) :
    ∃ (B' : Subgroup (MulAut (StatedProj (matrixDerived (oQ R')))))
      (y' : MulAut (StatedProj (matrixDerived (oQ R')))) (g' : similarityPairs (oQ R')),
      Sit (oQ R') B' (oκ _ g') y' ∧ g'.val.right = 1 ∧ g'.val.left = H⁻¹ * g.val.left * H := by
  obtain ⟨hS, hl, hr⟩ := exists_transport_of_gram hgram hg1
  have h' := h.transport H⁻¹ 1 hS
  rw [oTransport_kappa] at h'
  exact ⟨_, _, transPair H⁻¹ 1 hS g, h', hr, hl⟩

theorem split_false_core (hK : ringChar K ≠ 2) {R : GL (Fin (2 * 4)) K}
    (hR : (R : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)ᵀ = R) {A : GL (Fin (2 * 4)) K}
    (hA : A ∈ matrixIsometries (oQ R))
    (hAR : (A : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)ᵀ * R * A = R)
    (hA2 : (A : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) * A = 1)
    (h4 : 4 ≤ Module.finrank K (eigP (A : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)))
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ R))))}
    {y : MulAut (StatedProj (matrixDerived (oQ R)))} (h : Sit (oQ R) B (oκ _ (linPair A hA)) y) :
    False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨hab, c, hcA, horth, hdiag, -, hNFc⟩ := exists_split_nf hK hR hAR hA2
  obtain ⟨hw, S, hS, heq⟩ := exists_transport_of_family h2 hA hab c hcA horth hdiag
  have h' := h.transport S 1 hS
  rw [oTransport_kappa, heq] at h'
  exact sign_false hw hK (hNFc (by omega)) h'

theorem split_false (hK : ringChar K ≠ 2) {R : GL (Fin (2 * 4)) K}
    (hR : (R : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)ᵀ = R) {A : GL (Fin (2 * 4)) K}
    (hA : A ∈ matrixIsometries (oQ R))
    (hAR : (A : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)ᵀ * R * A = R)
    (hA2 : (A : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) * A = 1)
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ R))))}
    {y : MulAut (StatedProj (matrixDerived (oQ R)))} (h : Sit (oQ R) B (oκ _ (linPair A hA)) y) :
    False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hsum := finrank_eig_add h2 hA2
  by_cases h4 : 4 ≤ Module.finrank K (eigP (A : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K))
  · exact split_false_core hK hR hA hAR hA2 h4 h
  have hnegR : (-(A : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K))ᵀ * R *
      (-(A : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)) = R := by
    rw [transpose_neg, Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg, hAR]
  have hneg : -A ∈ matrixIsometries (oQ R) :=
    (mem_matrixIsometries_oQ h2 R hR (-A)).2 ((CatalogueBGraphForm.mem_isometryGroup _ _ _ _).2
      (by rw [Units.val_neg]; exact hnegR))
  have hnegA : GeneralLinearGroup.scalar (Fin (2 * 4)) (-1 : Kˣ) * (-A) = A := by
    apply Units.ext
    rw [Units.val_mul, Units.val_neg, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Units.val_neg, Units.val_one, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
      Matrix.one_mul, neg_one_smul, neg_neg]
  have hκneg : oκ _ (linPair A hA) = oκ _ (linPair (-A) hneg) := by
    refine oκ_eq_of_left_eq (c := -1) rfl ?_
    rw [linPair_left, linPair_left, hnegA]
  rw [hκneg] at h
  refine split_false_core hK hR hneg (by rw [Units.val_neg]; exact hnegR)
    (by rw [Units.val_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]; exact hA2) ?_ h
  rw [Units.val_neg, eigP_neg]
  omega

theorem inner_false (hK : ringChar K ≠ 2) {R : GL (Fin (2 * 4)) K}
    (hR : (R : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)ᵀ = R)
    (hdetR : IsSquare (R : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K).det) (hker : OKer (oQ R))
    {g : similarityPairs (oQ R)} (hg1 : g.val.right = 1) (hgg : oκ (oQ R) (g * g) = 1)
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ R))))}
    {y : MulAut (StatedProj (matrixDerived (oQ R)))} (h : Sit (oQ R) B (oκ _ g) y) : False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨c, hc0, hA2, hε, hμ⟩ := inner_even_data h2 hR (by norm_num) hker hg1 hgg
  rcases hε with hε | hε
  · by_cases hsq : IsSquare c
    ·
      obtain ⟨s, hs⟩ := hsq
      have hs0 : s ≠ 0 := by
        rintro rfl
        exact hc0 (by rw [hs, mul_zero])
      have hμc : (g.val.left : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)ᵀ * R * g.val.left =
          c • (R : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) := by
        rw [hε, one_smul, Matrix.mul_assoc, hA2, Matrix.mul_smul, Matrix.mul_one]
      obtain ⟨A', hA'def⟩ : ∃ A' : GL (Fin (2 * 4)) K,
          A' = GeneralLinearGroup.scalar (Fin (2 * 4)) (Units.mk0 s hs0)⁻¹ * g.val.left :=
        ⟨_, rfl⟩
      have hA'c : (A' : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) =
          s⁻¹ • (g.val.left : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) := by
        rw [hA'def, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
          ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul,
          Units.val_inv_eq_inv_val, Units.val_mk0]
      have hA'R : (A' : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)ᵀ * R * A' = R := by
        rw [hA'c, transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, hμc,
          smul_smul, smul_smul, hs]
        rw [show s⁻¹ * s⁻¹ * (s * s) = 1 by field_simp, one_smul]
      have hA'2 : (A' : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) * A' = 1 := by
        rw [hA'c, Matrix.smul_mul, Matrix.mul_smul, hA2, smul_smul, smul_smul, hs]
        rw [show s⁻¹ * s⁻¹ * (s * s) = 1 by field_simp, one_smul]
      have hA' : A' ∈ matrixIsometries (oQ R) :=
        (mem_matrixIsometries_oQ h2 R hR A').2
          ((CatalogueBGraphForm.mem_isometryGroup _ _ _ _).2 hA'R)
      have hκ : oκ _ g = oκ _ (linPair A' hA') := by
        refine oκ_eq_of_left_eq (c := Units.mk0 s hs0) (by rw [hg1, linPair_right]) ?_
        rw [linPair_left, hA'def, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
      rw [hκ] at h
      exact split_false hK hR hA' hA'R hA'2 h
    ·
      have : Fact (Irreducible (sqPoly c)) := ⟨irreducible_sqPoly hsq⟩
      obtain ⟨H, β, hβ0, hgram, hAH⟩ := exists_orth2_basis hK hR hsq hA2 hε
      obtain ⟨hEf, hE⟩ := finite_ringChar_EAlg hK hc0
      obtain ⟨P, w, hw, hw1, hP⟩ := exists_frame hE (by omega : 2 ≤ 4) (diagGL hβ0)
        (by rw [coe_diagGL]; exact diagonal_transpose _) (one_ne_zero (α := EAlg c))
      rw [coe_diagGL] at hP
      obtain ⟨S, hS⟩ : ∃ S, S = resGL (phiE c).toRingHom 4 P := ⟨_, rfl⟩
      obtain ⟨M, hM⟩ : ∃ M, M = H * S := ⟨_, rfl⟩
      obtain ⟨R₂, hR₂⟩ : ∃ R₂, R₂ = CatalogueBGraphForm.glTranspose (2 * 4) K M * R * M :=
        ⟨_, rfl⟩
      have hW : ∀ x, ((phiE c).toRingHom x)ᵀ * wMat 1 c = wMat 1 c * (phiE c).toRingHom
          (RingHom.id _ x) := fun x => transpose_phiE_mul_wOne hc0 x
      have hPid : (P : Matrix (Fin 4) (Fin 4) (EAlg c)).map (RingHom.id _) = P := by
        ext
        rfl
      have hgram₂ : (M : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)ᵀ * R * M = R₂ := by
        rw [hR₂]
        simp only [Units.val_mul, CatalogueBGraphForm.glTranspose_matrix]
      have hR₂m : (R₂ : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) =
          blkDiag 4 (wMat 1 c) * resMat (phiE c).toRingHom 4 (diagonal w) := by
        rw [← hgram₂, hM, Units.val_mul, transpose_mul, hS]
        change (resMat (phiE c).toRingHom 4 (P : Matrix (Fin 4) (Fin 4) (EAlg c)))ᵀ *
            (H : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)ᵀ * R *
              ((H : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *
                resMat (phiE c).toRingHom 4 (P : Matrix (Fin 4) (Fin 4) (EAlg c))) = _
        rw [show (resMat (phiE c).toRingHom 4 (P : Matrix (Fin 4) (Fin 4) (EAlg c)))ᵀ *
            (H : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)ᵀ * R *
              ((H : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *
                resMat (phiE c).toRingHom 4 (P : Matrix (Fin 4) (Fin 4) (EAlg c))) =
            (resMat (phiE c).toRingHom 4 (P : Matrix (Fin 4) (Fin 4) (EAlg c)))ᵀ *
              ((H : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)ᵀ * R * H) *
                resMat (phiE c).toRingHom 4 (P : Matrix (Fin 4) (Fin 4) (EAlg c)) by
          simp only [Matrix.mul_assoc], hgram, resMat_transpose_mul_mul hW, hPid, hP]
      have hdet₂ : IsSquare (R₂ : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K).det := by
        obtain ⟨r, hr⟩ := hdetR
        refine ⟨(M : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K).det * r, ?_⟩
        rw [← hgram₂, det_mul, det_mul, det_transpose, hr]
        ring
      obtain ⟨B', y', g', h', hg'1, hg'l⟩ := h.gram hgram₂ hg1
      have hSA : (S : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) * blkDiag 4 (jMat c) =
          blkDiag 4 (jMat c) * S := by
        have hj : jMat c = (phiE c).toRingHom (AdjoinRoot.root (sqPoly c)) := (phiE_root c).symm
        rw [hS, coe_resGL, hj, ← resMat_diagonal, ← map_mul, ← map_mul]
        congr 1
        ext i k
        rw [mul_diagonal, diagonal_mul, mul_comm]
      have hg'A : (g'.val.left : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = blkDiag 4 (jMat c) := by
        rw [hg'l, hM, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, Units.val_mul,
          Units.val_mul]
        have e1 := inv_mul_mul_eq hAH
        have e2 := inv_mul_mul_eq hSA.symm
        calc ((S⁻¹ : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *
              ((H⁻¹ : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *
              (g.val.left : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *
              ((H : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) * S) =
            ((S⁻¹ : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *
              (((H⁻¹ : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *
                (g.val.left : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) * H) * S := by
              simp only [Matrix.mul_assoc]
          _ = blkDiag 4 (jMat c) := by rw [e1, e2]
      exact orth2_false hK hsq hw hw1 hR₂m hdet₂ hg'1 hg'A h'
  ·
    obtain ⟨H₁, hgram₁, hAH₁⟩ := exists_pc_basis hK hR hc0 hA2 hε (fun _ => 1)
      (fun _ => one_ne_zero)
    obtain ⟨R₁, hR₁⟩ : ∃ R₁, R₁ = CatalogueBGraphForm.glTranspose (2 * 4) K H₁ * R * H₁ :=
      ⟨_, rfl⟩
    have hgramR₁ : (H₁ : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)ᵀ * R * H₁ = R₁ := by
      rw [hR₁]
      simp only [Units.val_mul, CatalogueBGraphForm.glTranspose_matrix]
    have hR₁m : (R₁ : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = blkDiag 4 (wMat 1 (-c)) := by
      rw [← hgramR₁, hgram₁]
      simp only [one_smul]
      rfl
    obtain ⟨B', y', g', h', hg'1, hg'l⟩ := h.gram hgramR₁ hg1
    have hg'A : (g'.val.left : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = blkDiag 4 (jMat c) := by
      rw [hg'l, Units.val_mul, Units.val_mul]
      exact inv_mul_mul_eq hAH₁
    by_cases hsq : IsSquare c
    · obtain ⟨s, hs⟩ := hsq
      have hs0 : s ≠ 0 := by
        rintro rfl
        exact hc0 (by rw [hs, mul_zero])
      have hcs : c = s ^ 2 := by rw [hs, sq]
      rw [hcs] at hR₁m hg'A
      exact pc_sq_false hK hs0 hR₁m hg'1 hg'A h'
    · exact pc_ns_false hK hsq hR₁m hg'1 hg'A h'

theorem field_false_of_pair (hK : ringChar K ≠ 2) {ℓ e : ℕ} (hℓ : ℓ.Prime) (he : 1 ≤ e)
    (hKc : Nat.card K = ℓ ^ e) {R : GL (Fin (2 * 4)) K}
    (hR : (R : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)ᵀ = R) (hker : OKer (oQ R))
    {g : similarityPairs (oQ R)} (hg1 : g.val.right ≠ 1) (hgg : oκ (oQ R) (g * g) = 1)
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ R))))}
    {y : MulAut (StatedProj (matrixDerived (oQ R)))} (h : Sit (oQ R) B (oκ _ g) y) : False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have : Fintype K := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hℓ2 : ℓ ≠ 2 := by rw [← ringChar.eq K ℓ]; exact hK
  obtain ⟨hσ2', c, hc⟩ := hker _ hgg
  have hσ2 : g.val.right ^ 2 = 1 := by rw [← (sq_val _ g).2]; exact hσ2'
  have hc' : g.val.left * glFieldAut (Fin (2 * 4)) K g.val.right g.val.left =
      GeneralLinearGroup.scalar (Fin (2 * 4)) c := by rw [← (sq_val _ g).1, hc]
  obtain ⟨e', hu, hσ⟩ := exists_unitaryFieldData_of_involution hℓ he hKc hσ2 hg1
  obtain ⟨wF, hwF, S, ν, hS, heq⟩ := exists_field_transport hu hℓ2 h2 (by omega) hR hσ hc'
  have h' := h.transport S ν hS
  rw [oTransport_kappa, heq] at h'
  exact field_false hu hℓ2 h2 hwF h'

theorem burgoyneD4TrialityOddCoreInput_holds : BurgoyneD4TrialityOddCoreInput := by
  intro K _ _ hK B hB t htB ht htN y hy
  by_contra hyN
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨ℓ, -, n, hℓ, hn⟩ := FiniteField.card' K
  have hKc : Nat.card K = ℓ ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hmod : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus 4 K))) .POmegaPlus 4 ℓ
      n := ⟨⟨hℓ, n.2, le_rfl⟩, K, inferInstance, inferInstance, hKc, ⟨MulEquiv.refl _⟩⟩
  have hs : Sit (Qc K) B t y :=
    ⟨conj_injective_coord, hB, hy, fun hF => hyN ((mem_familyAut_iff (Qc K) y).2 hF),
      d4Geom_coord, ptRigid_coord⟩
  have himage := coordinate_plus_family_eq_matrixImage hmod K hKc (MulEquiv.refl _)
  have htN' : t ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) := himage ▸ htN
  obtain ⟨g, hg⟩ := htN'
  obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (Qc K) (regular_coordinateQuadPlus 4 K (by omega)).1
  have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v) =
      ((1 : Kˣ) : K) * Qc K v := by
    intro v
    rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
  have hs₁ := hs.transport 1 1 hS₁
  have htg : t = oκ (Qc K) g := hg.symm
  rw [htg, oTransport_kappa] at hs₁
  have hker := (oKer_coordinatePlus hmod K hKc (MulEquiv.refl _)).transport 1 1 hS₁
  have hgg : oκ (oQ R) (transPair 1 1 hS₁ g * transPair 1 1 hS₁ g) = 1 := by
    have ht₁ : orderOf (oκ (oQ R) (transPair 1 1 hS₁ g)) = 2 := by
      rw [← oTransport_kappa]
      exact (MulEquiv.orderOf_eq (MulAut.congr (oTransport 1 1 hS₁)) (oκ (Qc K) g)).trans
        (htg ▸ ht)
    have hpow := pow_orderOf_eq_one (oκ (oQ R) (transPair 1 1 hS₁ g))
    rw [ht₁] at hpow
    rw [map_mul, ← pow_two]
    exact hpow
  by_cases hσ : (transPair 1 1 hS₁ g).val.right = 1
  · exact inner_false hK hR (isSquare_det_gram_coord h2 hR hRQ) hker hσ hgg hs₁
  · exact field_false_of_pair hK hℓ n.2 hKc hR hker hσ hgg hs₁

end CFSG.ComponentClassification.Burgoyne.D4

namespace CFSG.ComponentClassification.Burgoyne

theorem burgoyneD4TrialityOddCoreInput_holds : BurgoyneD4TrialityOddCoreInput :=
  D4.burgoyneD4TrialityOddCoreInput_holds

end CFSG.ComponentClassification.Burgoyne
