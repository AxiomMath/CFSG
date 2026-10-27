module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClOMem
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEvenInner
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOFieldNF
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClOField
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClOOrth2
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClOPcCore

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation (sq_val)
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL exists_frame OrthNF)

section Even

variable {K : Type} [Field K] [Finite K]

theorem ClO.commute_orth2_mem (hK : ringChar K ≠ 2) {n : ℕ} (hn : 4 ≤ n)
    {R : GL (Fin (2 * n)) K} (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R)
    (hker : OKer (oQ R))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ R)) →*
      MulAut (StatedProj (matrixDerived (oQ R)))))
    {g : similarityPairs (oQ R)} (hg1 : g.val.right = 1) {c : K} (hc : ¬ IsSquare c)
    (hA2 : (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * g.val.left = c • 1)
    (hAR : (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ * R =
      (1 : K) • ((R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * g.val.left))
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ R))))} (hRodd : Odd (Nat.card Ro))
    (hRi : ∀ y ∈ Ro, y * oκ _ g = oκ _ g * y)
    (hRc : ∀ s, oκ _ g s = s → Odd (orderOf s) → ∀ y ∈ Ro,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ Ro)
    (hsurj : ∀ y ∈ Ro, ∃ g' : similarityPairs (oQ R), y = oκ _ g') :
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
  refine ClO.commute_of_transport_mem M⁻¹ 1 hS' hRodd hRi hRc hsurj
    (fun R' hR'odd hR'i hR'c hR's => ?_)
  have h1 := ClO.orth2_eq_one hK hc hn hw hw1 hR₂s hR₂m (hker.transport M⁻¹ 1 hS')
    (ClO.conj_injective_of_mulEquiv (oTransport M⁻¹ 1 hS') hinj) hg'1 hg'A hR'odd hR'i hR'c hR's
  intro r₁ h₁ r₂ h₂
  rw [h1 r₁ h₁, h1 r₂ h₂]

theorem ClO.commute_pc_mem (hK : ringChar K ≠ 2) {ℓ e : ℕ} (hℓ : ℓ.Prime)
    (hKc : Nat.card K = ℓ ^ e) {n : ℕ} (hn : 4 ≤ n) {R : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R)
    (hker : OKer (oQ R))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ R)) →*
      MulAut (StatedProj (matrixDerived (oQ R)))))
    {g : similarityPairs (oQ R)} (hg1 : g.val.right = 1) {c : K} (hc : c ≠ 0)
    (hA2 : (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * g.val.left = c • 1)
    (hAR : (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ * R =
      (-1 : K) • ((R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * g.val.left))
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ R))))} (hRodd : Odd (Nat.card Ro))
    (hRi : ∀ y ∈ Ro, y * oκ _ g = oκ _ g * y)
    (hRc : ∀ s, oκ _ g s = s → Odd (orderOf s) → ∀ y ∈ Ro,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ Ro)
    (hsurj : ∀ y ∈ Ro, ∃ g' : similarityPairs (oQ R), y = oκ _ g') :
    ∀ r₁ ∈ Ro, ∀ r₂ ∈ Ro, r₁ * r₂ = r₂ * r₁ := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨H₁, hgram₁, hAH₁⟩ := exists_pc_basis hK hR hc hA2 hAR (fun _ => 1)
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
  obtain ⟨hS, hg₁l, hg₁1⟩ := exists_transport_of_gram hgramR₁ hg1
  have hg₁A : ((transPair H₁⁻¹ 1 hS g).val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
      blkDiag n (jMat c) := by
    rw [hg₁l, Units.val_mul, Units.val_mul]
    exact inv_mul_mul_eq hAH₁
  have hcd₁ : CompData ⁅isoCent R₁ (transPair H₁⁻¹ 1 hS g).val.left,
      isoCent R₁ (transPair H₁⁻¹ 1 hS g).val.left⁆ := by
    by_cases hsq : IsSquare c
    · obtain ⟨s, hs⟩ := hsq
      have hs0 : s ≠ 0 := by
        rintro rfl
        exact hc (by rw [hs, mul_zero])
      have hcs : c = s ^ 2 := by rw [hs, sq]
      exact compData_anti h2 hs0 (by omega) (by rw [hR₁m, hcs]) (by rw [hg₁A, hcs])
    · exact compData_unit hK hsq hℓ hKc (by omega) hR₁m hg₁A
  refine ClO.commute_of_transport_mem H₁⁻¹ 1 hS hRodd hRi hRc hsurj
    (fun R' hR'odd hR'i hR'c hsurj₁ => ?_)
  have hker₁ := hker.transport H₁⁻¹ 1 hS
  have hinj₁ := ClO.conj_injective_of_mulEquiv (oTransport H₁⁻¹ 1 hS) hinj
  have hform : ∀ y ∈ R', ∃ a : similarityPairs (oQ R₁), y = oκ _ a ∧ a.val.right = 1 ∧
      ∃ x z : K, (a.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
        x • 1 + z • blkDiag n (jMat c) := by
    intro y hy
    obtain ⟨a, rfl⟩ := hsurj₁ y hy
    obtain ⟨hr, x, z, hl⟩ := ClO.pc_core hK (by omega) hc hR₁m hker₁ hinj₁ hg₁1 hg₁A hcd₁
      hR'odd hR'i hR'c hy
    exact ⟨a, rfl, hr, x, z, hl⟩
  intro r₁ h₁ r₂ h₂
  obtain ⟨a, rfl, ha, x₁, z₁, hal⟩ := hform r₁ h₁
  obtain ⟨b, rfl, hb, x₂, z₂, hbl⟩ := hform r₂ h₂
  exact ClO.commute_lin ha hb hal hbl

theorem ClO.commute_inner_even_mem (hK : ringChar K ≠ 2) {ℓ e : ℕ} (hℓ : ℓ.Prime)
    (hKc : Nat.card K = ℓ ^ e) {n : ℕ} (hn : 4 ≤ n) {R : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R)
    (hker : OKer (oQ R))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ R)) →*
      MulAut (StatedProj (matrixDerived (oQ R)))))
    {g : similarityPairs (oQ R)} (hg1 : g.val.right = 1) (hi : orderOf (oκ _ g) = 2)
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ R))))} (hRodd : Odd (Nat.card Ro))
    (hRi : ∀ y ∈ Ro, y * oκ _ g = oκ _ g * y)
    (hRc : ∀ s, oκ _ g s = s → Odd (orderOf s) → ∀ y ∈ Ro,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ Ro)
    (hsurj : ∀ y ∈ Ro, ∃ g' : similarityPairs (oQ R), y = oκ _ g') :
    ∀ r₁ ∈ Ro, ∀ r₂ ∈ Ro, r₁ * r₂ = r₂ * r₁ := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hgg : oκ (oQ R) (g * g) = 1 := by
    have hp := pow_orderOf_eq_one (oκ (oQ R) g)
    rw [hi] at hp
    rw [map_mul, ← pow_two]
    exact hp
  obtain ⟨c, hc0, hA2, hε, hμ⟩ := inner_even_data h2 hR (by omega) hker hg1 hgg
  rcases hε with hε | hε
  · by_cases hsq : IsSquare c
    ·
      obtain ⟨s, hs⟩ := hsq
      have hs0 : s ≠ 0 := by
        rintro rfl
        exact hc0 (by rw [hs, mul_zero])
      have hμc : (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ * R * g.val.left =
          c • (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) := by
        rcases hμ with h | h
        · exact h
        · exfalso
          have e1 : (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ * R * g.val.left =
              c • (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) := by
            rw [hε, one_smul, Matrix.mul_assoc, hA2, Matrix.mul_smul, Matrix.mul_one]
          rw [h] at e1
          have e2 : ((2 : K) * c) • (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = 0 := by
            rw [mul_smul, two_smul]
            nth_rewrite 1 [← e1]
            rw [neg_smul, neg_add_cancel]
          rcases smul_eq_zero.1 e2 with h' | h'
          · exact mul_ne_zero h2 hc0 h'
          · have : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
            have := congrArg Matrix.det h'
            rw [det_zero] at this
            exact (Matrix.isUnits_det_units R).ne_zero this
      obtain ⟨A', hA'def⟩ : ∃ A' : GL (Fin (2 * n)) K,
          A' = GeneralLinearGroup.scalar (Fin (2 * n)) (Units.mk0 s hs0)⁻¹ * g.val.left :=
        ⟨_, rfl⟩
      have hA'c : (A' : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
          s⁻¹ • (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) := by
        rw [hA'def, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
          ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul,
          Units.val_inv_eq_inv_val, Units.val_mk0]
      have hA'R : (A' : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ * R * A' = R := by
        rw [hA'c, transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, hμc,
          smul_smul, smul_smul, hs]
        rw [show s⁻¹ * s⁻¹ * (s * s) = 1 by field_simp, one_smul]
      have hA'2 : (A' : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * A' = 1 := by
        rw [hA'c, Matrix.smul_mul, Matrix.mul_smul, hA2, smul_smul, smul_smul, hs]
        rw [show s⁻¹ * s⁻¹ * (s * s) = 1 by field_simp, one_smul]
      have hA' : A' ∈ matrixIsometries (oQ R) :=
        (mem_matrixIsometries_oQ h2 R hR A').2
          ((CatalogueBGraphForm.mem_isometryGroup _ _ _ _).2 hA'R)
      have hκ : oκ _ g = oκ _ (linPair A' hA') := by
        refine oκ_eq_of_left_eq (c := Units.mk0 s hs0) (by rw [hg1, linPair_right]) ?_
        rw [linPair_left, hA'def, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
      exact ClO.commute_split_mem hK (by omega) hR hker hinj hi hRodd hRi hRc hsurj hA' hκ hA'R
        hA'2
    · exact ClO.commute_orth2_mem hK hn hR hker hinj hg1 hsq hA2 hε hRodd hRi hRc hsurj
  · exact ClO.commute_pc_mem hK hℓ hKc hn hR hker hinj hg1 hc0 hA2 hε hRodd hRi hRc hsurj

end Even

variable {K : Type} [Field K] {d : ℕ}

theorem ClO.commute_field_mem [Finite K] (hK : ringChar K ≠ 2) (hd5 : 5 ≤ d) {ℓ e : ℕ}
    (hℓ : ℓ.Prime) (he : 1 ≤ e) (hKc : Nat.card K = ℓ ^ e) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) (hker : OKer (oQ R))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ R)) →*
      MulAut (StatedProj (matrixDerived (oQ R)))))
    {g : similarityPairs (oQ R)} (hg1 : g.val.right ≠ 1) (hi : orderOf (oκ _ g) = 2)
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ R))))} (hRodd : Odd (Nat.card Ro))
    (hRi : ∀ y ∈ Ro, y * oκ _ g = oκ _ g * y)
    (hRc : ∀ s, oκ _ g s = s → Odd (orderOf s) → ∀ y ∈ Ro,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ Ro)
    (hsurj : ∀ y ∈ Ro, ∃ g' : similarityPairs (oQ R), y = oκ _ g') :
    ∀ r₁ ∈ Ro, ∀ r₂ ∈ Ro, r₁ * r₂ = r₂ * r₁ := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have : Fintype K := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hℓ2 : ℓ ≠ 2 := by rw [← ringChar.eq K ℓ]; exact hK
  have hgg : oκ (oQ R) (g * g) = 1 := by
    rw [map_mul, ← pow_two, ← hi, pow_orderOf_eq_one]
  obtain ⟨hσ2', c, hc⟩ := hker _ hgg
  have hσ2 : g.val.right ^ 2 = 1 := by rw [← (sq_val _ g).2]; exact hσ2'
  have hc' : g.val.left * glFieldAut (Fin d) K g.val.right g.val.left =
      GeneralLinearGroup.scalar (Fin d) c := by rw [← (sq_val _ g).1, hc]
  obtain ⟨e', hu, hσ⟩ := exists_unitaryFieldData_of_involution hℓ he hKc hσ2 hg1
  obtain ⟨wF, hwF, S, ν, hS, heq⟩ := exists_field_transport hu hℓ2 h2 (by omega) hR hσ hc'
  refine ClO.commute_of_transport_mem S ν hS hRodd hRi hRc hsurj
    (fun R' hR'odd hR'i hR'c hR's => ?_)
  rw [heq] at hR'i hR'c
  have h1 := ClO.field_eq_one hu hℓ2 h2 hd5 hwF (hker.transport S ν hS)
    (ClO.conj_injective_of_mulEquiv (oTransport S ν hS) hinj) hR'odd hR'i hR'c hR's
  intro r₁ h₁ r₂ h₂
  rw [h1 r₁ h₁, h1 r₂ h₂]

end CFSG.ComponentClassification.Foote5.OddLieCore
