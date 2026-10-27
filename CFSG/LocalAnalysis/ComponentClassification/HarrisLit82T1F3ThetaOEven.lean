module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEvenInner
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3ThetaOTorus
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat
  conj_injective_of_mulEquiv eq_bot_of_oddCoreIn)

variable {K : Type} [Field K] {d : ℕ} [Finite K]

theorem inner_split_pow_eq_one (hK : ringChar K ≠ 2) {ℓ e : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hKc : Nat.card K = ℓ ^ e) (hℓ2 : ℓ ≠ 2) (hd7 : 7 ≤ d)
    {R : GL (Fin d) K} (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) (hker : OKer (oQ R))
    {X : Type} [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (θ : GeneralizedFitting.subgroup X ≃* StatedProj (matrixDerived (oQ R)))
    {t : X} (hsurj : OSurjX θ t) (ht : orderOf t = 2) {g : similarityPairs (oQ R)}
    (htg : socleAction θ t = oκ _ g) {A' : GL (Fin d) K}
    (hA' : A' ∈ matrixIsometries (oQ R)) (hκ : oκ _ g = oκ _ (linPair A' hA'))
    (hAR : (A' : Matrix (Fin d) (Fin d) K)ᵀ * R * A' = R)
    (hA2 : (A' : Matrix (Fin d) (Fin d) K) * A' = 1) {y : X}
    (hy : y ∈ oddCentralizerCore t) : y ^ (Nat.card K ^ 2 - 1) = 1 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hψ := socleAction_injective hsimple hnab θ
  set Rm := (R : Matrix (Fin d) (Fin d) K) with hRm
  obtain ⟨Am, hAm⟩ : ∃ Am : Matrix (Fin d) (Fin d) K, Am = A' := ⟨_, rfl⟩
  rw [← hAm] at hAR hA2
  have htrans : ∀ (A'' : GL (Fin d) K) (hA'' : A'' ∈ matrixIsometries (oQ R)),
      oκ _ g = oκ _ (linPair A'' hA'') → ∀ {a b : ℕ} (hab : a + b = d)
      (c : Fin a ⊕ Fin b → Fin d → K),
      (∀ x, (A'' : Matrix (Fin d) (Fin d) K) *ᵥ c x =
        (if x.isLeft then (-1 : K) else 1) • c x) →
      (∀ x y, x ≠ y → c x ⬝ᵥ Rm *ᵥ c y = 0) → (∀ x, c x ⬝ᵥ Rm *ᵥ c x ≠ 0) →
      (∀ (hw : ∀ l, famW Rm hab c l ≠ 0), OKer (oQ (diagGL hw)) →
        Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
          MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))) →
        ∀ {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))},
        (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
          MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))).range ≤ B →
        OSurjCore B (oκ _ (sgnPair h2 hw (famJ hab))) →
        ∀ y' ∈ oddCoreIn B (oκ _ (sgnPair h2 hw (famJ hab))), y' ^ (Nat.card K ^ 2 - 1) = 1) →
      y ^ (Nat.card K ^ 2 - 1) = 1 := by
    intro A'' hA'' hκ'' a b hab c hcA horth hdiag hcase
    obtain ⟨hw, S, hS, heq⟩ := exists_transport_of_family h2 hA'' hab c hcA horth hdiag
    have hψ't : socleAction (θ.trans (oTransport S 1 hS)) t =
        oκ _ (sgnPair h2 hw (famJ hab)) := by
      rw [socleAction_trans, htg, hκ'', oTransport_kappa, heq]
    refine pow_eq_one_of_transfer
      (socleAction_injective hsimple hnab (θ.trans (oTransport S 1 hS))) (fun y' hy' => ?_) hy
    rw [hψ't] at hy'
    exact hcase hw (hker.transport S 1 hS)
      (conj_injective_of_mulEquiv hsimple hnab (θ.trans (oTransport S 1 hS)))
      (by rintro _ ⟨x, rfl⟩; exact conj_mem_range_socleAction _ x)
      (((hsurj.transport S 1 hS).core hsimple hnab).of_eq hψ't) y' hy'
  have hslice : ∀ (A'' : GL (Fin d) K) (hA'' : A'' ∈ matrixIsometries (oQ R)),
      oκ _ g = oκ _ (linPair A'' hA'') →
      (A'' : Matrix (Fin d) (Fin d) K)ᵀ * Rm * A'' = Rm →
      (A'' : Matrix (Fin d) (Fin d) K) * A'' = 1 →
      Module.finrank K (eigM (A'' : Matrix (Fin d) (Fin d) K)) = 2 →
      y ^ (Nat.card K ^ 2 - 1) = 1 := by
    intro A'' hA'' hκ'' hAR'' hA2'' hM2''
    have hsum := finrank_eig_add h2 hA2''
    rw [hM2''] at hsum
    by_cases h3 : Nat.card K = 3
    ·
      obtain ⟨hab, c, hcA, horth, hdiag, -, hNFc⟩ := exists_split_nf hK hR hAR'' hA2''
      refine htrans A'' hA'' hκ'' hab c hcA horth hdiag
        fun hw hker' hinj' B hB hsurj' y' hy' => ?_
      have hJcard : (famJ hab).card = 2 := by rw [card_famJ hab, hM2'']
      have hJccard : (famJ hab)ᶜ.card =
          Module.finrank K (eigP (A'' : Matrix (Fin d) (Fin d) K)) := by
        rw [Finset.card_compl, Fintype.card_fin, card_famJ hab]
        omega
      rw [split_two_oddCoreIn_eq_bot_three_gen h3 hK hw hker' hsurj' hinj' hB hJcard
        ((hNFc (by omega)).blockOK (by omega) fun h => by omega), mem_bot] at hy'
      rw [hy', one_pow]
    · have hK5 : 5 ≤ Nat.card K := by
        have hodd := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK
        have h1 : 2 ≤ Nat.card K := Finite.one_lt_card
        obtain ⟨k, hk⟩ := hodd
        omega
      obtain ⟨hab, c, hcA, horth, hdiag, β, γ, hβ0, hγ0, hβ1, hγ1, h0, h1, h2', hr, hL⟩ :=
        exists_slice_nf_gen hK hR hAR'' hA2'' hM2'' (by omega)
      obtain ⟨-, I₀, hI₀, hI₀3, hI₀w, hns⟩ := sliceW_of_nf_gen hab (by omega) hβ0 hβ1 hγ1
        h0 h1 h2' hr hL
      refine htrans A'' hA'' hκ'' hab c hcA horth hdiag
        fun hw hker' hinj' B hB hsurj' y' hy' => ?_
      have hJ : famJ hab = jSet := by
        ext l
        rw [mem_famJ, mem_jSet]
      rw [hJ] at hsurj' hy'
      have hJ2 : (jSet : Finset (Fin d)).card = 2 := card_jSet (by omega)
      have hJc3 : 3 ≤ (jSet : Finset (Fin d))ᶜ.card := by
        rw [Finset.card_compl, Fintype.card_fin, hJ2]
        omega
      obtain ⟨g', rfl⟩ := hsurj' y' hy'
      obtain ⟨hτ, -, hiso⟩ := iso_of_mix hK hK5 hw hker' hinj' hB (Or.inr rfl) hJc3 hI₀ hI₀3
        hI₀w hns hy'
      obtain ⟨R', hR', hRJ, hgR⟩ := exists_oIsoBlock_of_iso hK hw hker'
        (Finset.card_pos.1 (by omega)) hy' hτ hiso
      rw [hgR]
      exact oκ_linPair_pow_card_sq_sub_one hKc hℓ2 hw hJ2 hR' hRJ
  have hκ1 : oκ (oQ R) g ≠ 1 := by
    intro h1
    rw [h1, ← map_one (socleAction θ)] at htg
    have := hψ htg
    rw [this, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hnegR : (-Am)ᵀ * Rm * (-Am) = Rm := by
    rw [transpose_neg, Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg, hAR]
  have hneg : -A' ∈ matrixIsometries (oQ R) :=
    (mem_matrixIsometries_oQ h2 R hR (-A')).2 ((CatalogueBGraphForm.mem_isometryGroup _ _ _ _).2
      (by rw [Units.val_neg, ← hAm]; exact hnegR))
  have hnegA : GeneralLinearGroup.scalar (Fin d) (-1 : Kˣ) * (-A') = A' := by
    apply Units.ext
    rw [Units.val_mul, Units.val_neg, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Units.val_neg, Units.val_one, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
      Matrix.one_mul, neg_one_smul, neg_neg]
  have hκneg : oκ _ g = oκ _ (linPair (-A') hneg) := by
    rw [hκ]
    refine oκ_eq_of_left_eq (c := -1) rfl ?_
    rw [linPair_left, linPair_left, hnegA]
  have hsum := finrank_eig_add h2 hA2
  have hM1 : 1 ≤ Module.finrank K (eigM Am) := by
    by_contra h0
    have hbot : eigM Am = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
    have htop : eigP Am = ⊤ := by
      have := (isCompl_eig h2 hA2).sup_eq_top
      rwa [hbot, sup_bot_eq] at this
    have h1 : Am = 1 := eq_one_of_forall_mulVec fun v => mem_eigP.1 (htop ▸ Submodule.mem_top)
    apply hκ1
    rw [hκ]
    have : linPair A' hA' = 1 := by
      apply Subtype.ext
      apply SemidirectProduct.ext
      · exact Units.ext (by rw [linPair_left, ← hAm]; exact h1)
      · rfl
    rw [this, map_one]
  have hP1 : 1 ≤ Module.finrank K (eigP Am) := by
    by_contra h0
    have hbot : eigP Am = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
    have htop : eigM Am = ⊤ := by
      have := (isCompl_eig h2 hA2).sup_eq_top
      rwa [hbot, bot_sup_eq] at this
    have h1 : -Am = 1 := eq_one_of_forall_mulVec fun v => by
      rw [neg_mulVec, mem_eigM.1 (htop ▸ Submodule.mem_top), neg_neg]
    apply hκ1
    rw [hκneg]
    have : linPair (-A') hneg = 1 := by
      apply Subtype.ext
      apply SemidirectProduct.ext
      · exact Units.ext (by rw [linPair_left, Units.val_neg, ← hAm]; exact h1)
      · rfl
    rw [this, map_one]
  by_cases hM2 : Module.finrank K (eigM Am) = 2
  · exact hslice A' hA' hκ (by rw [← hAm]; exact hAR) (by rw [← hAm]; exact hA2)
      (by rw [← hAm]; exact hM2)
  by_cases hP2 : Module.finrank K (eigP Am) = 2
  · refine hslice (-A') hneg hκneg (by rw [Units.val_neg, ← hAm]; exact hnegR)
      (by rw [Units.val_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg, ← hAm]; exact hA2) ?_
    rw [Units.val_neg, ← hAm, eigM_neg]
    exact hP2
  obtain ⟨hab, c, hcA, horth, hdiag, hNF, hNFc⟩ := exists_split_nf hK hR hAR hA2
  refine htrans A' hA' hκ hab c (by rw [← hAm]; exact hcA) horth hdiag
    fun hw hker' hinj' B hB hsurj' y' hy' => ?_
  have hJcard : (famJ hab).card = Module.finrank K (eigM Am) := card_famJ hab
  have hJccard : (famJ hab)ᶜ.card = Module.finrank K (eigP Am) := by
    rw [Finset.card_compl, Fintype.card_fin, hJcard]
    omega
  rw [split_oddCoreIn_eq_bot_of_nf_gen hK hd7 hw hker' hsurj' hinj' hB
    (by omega) (by omega) (by omega) (by omega) (fun h3 => hNF (by omega))
    (fun h3 => hNFc (by omega)), mem_bot] at hy'
  rw [hy', one_pow]

theorem pc_pow_eq_one (hK : ringChar K ≠ 2) {ℓ e : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hKc : Nat.card K = ℓ ^ e) (hℓ2 : ℓ ≠ 2) {n : ℕ} (hn : 4 ≤ n)
    {R : GL (Fin (2 * n)) K} (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R)
    (hker : OKer (oQ R)) {X : Type} [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (θ : GeneralizedFitting.subgroup X ≃* StatedProj (matrixDerived (oQ R)))
    {t : X} (hsurj : OSurjX θ t) {g : similarityPairs (oQ R)} (hg1 : g.val.right = 1)
    (htg : socleAction θ t = oκ _ g) {c : K} (hc : c ≠ 0)
    (hA2 : (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * g.val.left = c • 1)
    (hAR : (g.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ * R =
      (-1 : K) • ((R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * g.val.left))
    {y : X} (hy : y ∈ oddCentralizerCore t) : y ^ (Nat.card K ^ 2 - 1) = 1 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set A₁ := blkDiag n (jMat c) with hA₁
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
  obtain ⟨θ₁, g₁, hg₁1, hg₁l, htg₁, hker₁, hsurj₁, -, hinj₁, hB₁⟩ :=
    exists_model hker hsimple hnab θ hsurj hg1 htg hgramR₁
  have hg₁A : (g₁.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = A₁ := by
    rw [hg₁l, Units.val_mul, Units.val_mul]
    exact inv_mul_mul_eq hAH₁
  have hcd₁ : CompData ⁅isoCent R₁ g₁.val.left, isoCent R₁ g₁.val.left⁆ := by
    by_cases hsq : IsSquare c
    · obtain ⟨s, hs⟩ := hsq
      have hs0 : s ≠ 0 := by
        rintro rfl
        exact hc (by rw [hs, mul_zero])
      have hcs : c = s ^ 2 := by rw [hs, sq]
      exact compData_anti h2 hs0 (by omega) (by rw [hR₁m, hcs]) (by rw [hg₁A, hA₁, hcs])
    · exact compData_unit hK hsq (Fact.out : ℓ.Prime) hKc (by omega) hR₁m hg₁A
  have hψ₁ := socleAction_injective hsimple hnab θ₁
  apply hψ₁
  rw [map_pow, map_one]
  have hmem : socleAction θ₁ y ∈ oddCoreIn (socleAction θ₁).range (oκ _ g₁) := by
    rw [← htg₁, ← map_oddCentralizerCore_of_injective hψ₁]
    exact ⟨y, hy, rfl⟩
  obtain ⟨g', hg'⟩ := hsurj₁ y hy
  rw [hg'] at hmem ⊢
  obtain ⟨hr, α, β, hl⟩ := pc_core hK (by omega) hc hR₁m hker₁ hinj₁ hB₁ hg₁1 hg₁A hcd₁ hmem
  have : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
  have hA₁2 : A₁ * A₁ = c • 1 := by
    rw [hA₁, blkDiag_mul, jMat_mul_self, blkDiag_smul, blkDiag_one']
  exact oκ_pow_card_sq_sub_one_of_sq hKc hℓ2 hr hc hA₁2 hl

theorem inner_even_pow_eq_one (hK : ringChar K ≠ 2) {ℓ e : ℕ} (hℓ : ℓ.Prime)
    (hKc : Nat.card K = ℓ ^ e) {n : ℕ} (hn : 4 ≤ n) {R : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R)
    (hker : OKer (oQ R)) {X : Type} [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (θ : GeneralizedFitting.subgroup X ≃* StatedProj (matrixDerived (oQ R)))
    {t : X} (hsurj : OSurjX θ t) (ht : orderOf t = 2) {g : similarityPairs (oQ R)}
    (hg1 : g.val.right = 1) (htg : socleAction θ t = oκ _ g) {y : X}
    (hy : y ∈ oddCentralizerCore t) : y ^ (Nat.card K ^ 2 - 1) = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hℓ2 : ℓ ≠ 2 := by rw [← ringChar.eq K ℓ]; exact hK
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hgg : oκ (oQ R) (g * g) = 1 := by
    rw [map_mul, ← htg, ← map_mul, ← pow_two,
      show t ^ 2 = 1 from by rw [← ht]; exact pow_orderOf_eq_one t, map_one]
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
      exact inner_split_pow_eq_one hK hKc hℓ2 (by omega) hR hker hsimple hnab θ hsurj ht htg hA'
        hκ hA'R hA'2 hy
    · rw [orth2_oddCentralizerCore_eq_bot hK hn hR hker hsimple hnab θ hsurj hg1 htg hsq hA2 hε,
        mem_bot] at hy
      rw [hy, one_pow]
  · exact pc_pow_eq_one hK hKc hℓ2 hn hR hker hsimple hnab θ hsurj hg1 htg hc0 hA2 hε hy

end CFSG.ComponentClassification.Burgoyne.O
