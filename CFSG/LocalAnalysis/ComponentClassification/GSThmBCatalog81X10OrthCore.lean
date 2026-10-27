module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10OrthO2Ns
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10OrthField
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEvenInner
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOFieldNF
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEvenModel
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXDrField
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXKlOrth2
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10OrthO2
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10OrthO2Split
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10OrthPc

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.X10Orth

open Module Matrix CFSG Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation (sq_val)
open CFSG.ComponentClassification.Burgoyne CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (signMat diagGL coe_diagGL)

variable {K : Type} [Field K]

theorem even_of_skew (h2 : (2 : K) ≠ 0) {d : ℕ} {R S : GL (Fin d) K}
    (hSR : (S : Matrix (Fin d) (Fin d) K)ᵀ * R = (-1 : K) • ((R : Matrix (Fin d) (Fin d) K) * S)) :
    Even d := by
  by_contra hodd
  have hodd' : Odd d := Nat.not_even_iff_odd.1 hodd
  have e := congrArg Matrix.det hSR
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Matrix.det_mul, Fintype.card_fin,
    hodd'.neg_one_pow] at e
  have hS := (Matrix.isUnits_det_units S).ne_zero
  have hR := (Matrix.isUnits_det_units R).ne_zero
  have : (2 : K) * ((S : Matrix (Fin d) (Fin d) K).det * (R : Matrix (Fin d) (Fin d) K).det) =
      0 := by linear_combination e
  rcases mul_eq_zero.1 this with h | h
  · exact h2 h
  · exact mul_ne_zero hS hR h

theorem even_of_nonsquare {d : ℕ} {S : GL (Fin d) K} {c : K} (hc : ¬ IsSquare c)
    (hS2 : (S : Matrix (Fin d) (Fin d) K) * S = c • 1) : Even d := by
  by_contra hodd
  obtain ⟨m, rfl⟩ := Nat.not_even_iff_odd.1 hodd
  have hc0 : c ≠ 0 := fun h => hc ⟨0, by rw [h, mul_zero]⟩
  have e := congrArg Matrix.det hS2
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at e
  apply hc
  have hcm : c ^ m ≠ 0 := pow_ne_zero _ hc0
  refine ⟨(S : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K).det / c ^ m, ?_⟩
  field_simp
  calc c * (c ^ m) ^ 2 = c ^ (2 * m + 1) := by ring
    _ = _ := by rw [← e]; ring

theorem oκ_sgnPair_eq_one {d : ℕ} (h2 : (2 : K) ≠ 0) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {J : Finset (Fin d)} (hJ : J = ∅ ∨ J = Finset.univ) : oκ _ (sgnPair h2 hw J) = 1 := by
  rw [← map_one (oκ (oQ (diagGL hw)))]
  rcases hJ with rfl | rfl
  · refine oκ_eq_of_left_eq (c := 1) rfl ?_
    rw [map_one, one_mul]
    exact C.signGL_empty
  · refine oκ_eq_of_left_eq (c := -1) rfl ?_
    apply Units.ext
    change signMat K Finset.univ = _
    ext i j
    simp [signMat, Matrix.diagonal_apply]

variable [Finite K]

theorem card_of_inner (hK : ringChar K ≠ 2) {ℓ e : ℕ} (hℓ : ℓ.Prime) (hKc : Nat.card K = ℓ ^ e)
    {d : ℕ} (hd : 7 ≤ d) {R : GL (Fin d) K} (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R)
    (hker : OKer (oQ R)) {gs : similarityPairs (oQ R)} (hσ : gs.val.right = 1)
    (hss : oκ _ (gs * gs) = 1) (hs1 : oκ _ gs ≠ 1) {M : Subgroup (GL (Fin d) K)} {Q : ℕ}
    (h : X10Data R gs M Q) (hQ : Odd Q) : d = 8 ∧ Nat.card K ^ 4 = Q := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set S := gs.val.left with hSdef
  set Sm := (S : Matrix (Fin d) (Fin d) K) with hSm
  set Rm := (R : Matrix (Fin d) (Fin d) K) with hRm
  obtain ⟨c, hc0, hS2, hε, -⟩ := inner_even_data h2 hR (by omega) hker hσ hss
  rcases hε with hε | hε
  swap
  ·
    exfalso
    obtain ⟨n, hn⟩ := even_of_skew h2 hε
    obtain rfl : d = 2 * n := by omega
    obtain ⟨H₁, hgram₁, hAH₁⟩ := exists_pc_basis hK hR hc0 hS2 hε (fun _ => 1)
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
    have hgA : ((transPair H₁⁻¹ 1 hS gs).val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
        blkDiag n (jMat c) := by
      rw [hl, Units.val_mul, Units.val_mul]
      exact inv_mul_mul_eq hAH₁
    exact false_of_pc hK hℓ hKc hc0 (by omega) hR₁m hr hgA (h.transport H₁⁻¹ 1 hS)
  by_cases hsq : IsSquare c
  swap
  ·
    obtain ⟨n, hn⟩ := even_of_nonsquare hsq hS2
    obtain rfl : d = 2 * n := by omega
    have : Fact (Irreducible (sqPoly c)) := ⟨irreducible_sqPoly hsq⟩
    obtain ⟨w, hw, hw1, R₂, gs₂, M₂, hR₂s, hR₂m, hker₂, hσ₂, hgA₂, h₂, -⟩ :=
      exists_orth2_model hK (by omega) hR hker hσ hsq hS2 hε h
    rcases Nat.lt_or_ge 4 n with h5 | h4
    · exact (false_of_orth2_five hK hsq h5 hw hw1 hR₂s hR₂m hσ₂ hgA₂ h₂).elim
    · obtain rfl : n = 4 := by omega
      refine ⟨rfl, ?_⟩
      by_cases hS : ∃ T : Submodule (EAlg c) (Fin 4 → EAlg c), Module.finrank (EAlg c) T = 2 ∧
          ∀ x ∈ T, CatalogueBLinearHigherB.matrixQuadraticForm (diagGL hw) x = 0
      · exact (false_of_orth2_split hK hsq hw hR₂s hR₂m hker₂ hσ₂ hgA₂ h₂ hS).elim
      · exact card_of_orth2_nonsplit hK hsq hw hR₂s hR₂m hσ₂ hgA₂ h₂ hQ hS
  exfalso
  have hSR : Smᵀ * Rm * Sm = c • Rm := by
    rw [hε, one_smul, Matrix.mul_assoc, hS2, Matrix.mul_smul, Matrix.mul_one]
  obtain ⟨s₀, hs₀⟩ := hsq
  have hs₀0 : s₀ ≠ 0 := by
    rintro rfl
    exact hc0 (by rw [hs₀, mul_zero])
  obtain ⟨S', hS'def⟩ : ∃ S' : GL (Fin d) K,
      S' = GeneralLinearGroup.scalar (Fin d) (Units.mk0 s₀ hs₀0)⁻¹ * S := ⟨_, rfl⟩
  have hS'c : (S' : Matrix (Fin d) (Fin d) K) = s₀⁻¹ • Sm := by
    rw [hS'def, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul,
      Units.val_inv_eq_inv_val, Units.val_mk0]
  have hS'R : (S' : Matrix (Fin d) (Fin d) K)ᵀ * Rm * S' = Rm := by
    rw [hS'c, transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, hSR,
      smul_smul, smul_smul, hs₀]
    rw [show s₀⁻¹ * s₀⁻¹ * (s₀ * s₀) = 1 by field_simp, one_smul]
  have hS'2 : (S' : Matrix (Fin d) (Fin d) K) * S' = 1 := by
    rw [hS'c, Matrix.smul_mul, Matrix.mul_smul, hS2, smul_smul, smul_smul, hs₀]
    rw [show s₀⁻¹ * s₀⁻¹ * (s₀ * s₀) = 1 by field_simp, one_smul]
  have hS' : S' ∈ matrixIsometries (oQ R) :=
    (mem_matrixIsometries_oQ h2 R hR S').2
      ((CatalogueBGraphForm.mem_isometryGroup _ _ _ _).2 hS'R)
  have hκ : oκ _ gs = oκ _ (linPair S' hS') := by
    refine oκ_eq_of_left_eq (c := Units.mk0 s₀ hs₀0) (by rw [hσ, linPair_right]) ?_
    rw [linPair_left, hS'def, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have h' := h.of_kappa_eq hκ
  rw [hκ] at hs1
  obtain ⟨hab, cfr, hcA, horth, hdiag, hNF₁, hNF₂⟩ := exists_split_nf hK hR hS'R hS'2
  obtain ⟨hw, Str, hStr, heq⟩ := exists_transport_of_family h2 hS' hab cfr hcA horth hdiag
  set w := famW Rm hab cfr with hwdef
  set J := famJ hab with hJdef
  have hd' := h'.transport Str 1 hStr
  rw [heq] at hd'
  have hne : oκ _ (sgnPair h2 hw J) ≠ 1 := by
    rw [hJdef, ← heq, ← oTransport_kappa]
    intro h1
    apply hs1
    exact (MulAut.congr (oTransport Str 1 hStr)).injective (by rw [h1, map_one])
  have hJ : J.Nonempty :=
    Finset.nonempty_iff_ne_empty.2 fun h => hne (oκ_sgnPair_eq_one h2 hw (Or.inl h))
  have hJc : Jᶜ.Nonempty := Finset.nonempty_iff_ne_empty.2 fun h =>
    hne (oκ_sgnPair_eq_one h2 hw (Or.inr (Finset.compl_eq_empty_iff _ |>.1 h)))
  have hNF : ∀ I : Finset (Fin d), (I = J ∨ I = Jᶜ) → 3 ≤ I.card → BlockNF w I := by
    rintro I (rfl | rfl) h3
    · exact hNF₁ (by rw [hJdef, card_famJ] at h3; exact h3)
    · apply hNF₂
      rw [Finset.card_compl, Fintype.card_fin, hJdef, card_famJ] at h3
      omega
  exact false_of_sign hK hd hw (hker.transport Str 1 hStr) hJ hJc hNF hd'

theorem card_of_x10 (hK : ringChar K ≠ 2) {ℓ e : ℕ} (hℓ : ℓ.Prime) (he : 1 ≤ e)
    (hKc : Nat.card K = ℓ ^ e) {d : ℕ} (hd : 7 ≤ d) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) (hker : OKer (oQ R))
    {gs : similarityPairs (oQ R)} (hss : oκ _ (gs * gs) = 1) (hs1 : oκ _ gs ≠ 1)
    {M : Subgroup (GL (Fin d) K)} {Q : ℕ} (h : X10Data R gs M Q) (hQ : Odd Q) :
    d = 8 ∧ Nat.card K ^ 4 = Q := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  by_cases hσ : gs.val.right = 1
  · exact card_of_inner hK hℓ hKc hd hR hker hσ hss hs1 h hQ
  exfalso
  have : Fintype K := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hℓ2 : ℓ ≠ 2 := by rw [← ringChar.eq K ℓ]; exact hK
  obtain ⟨hσ2', c, hc⟩ := hker _ hss
  have hσ2 : gs.val.right ^ 2 = 1 := by rw [← (sq_val _ gs).2]; exact hσ2'
  have hc' : gs.val.left * glFieldAut (Fin d) K gs.val.right gs.val.left =
      GeneralLinearGroup.scalar (Fin d) c := by rw [← (sq_val _ gs).1, hc]
  obtain ⟨e', hu, hσ'⟩ := exists_unitaryFieldData_of_involution hℓ he hKc hσ2 hσ
  obtain ⟨wF, hwF, S, ν, hS, heq⟩ :=
    exists_field_transport hu hℓ2 h2 (by omega) hR hσ' hc'
  exact false_of_field hu hK hℓ2 hd hwF ((h.transport S ν hS).of_kappa_eq heq)

end CFSG.ComponentClassification.GSThmB.X10Orth
