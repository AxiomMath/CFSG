module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBOOddNF
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEvenSliceNF
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOGenCases

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat
  conj_injective_of_mulEquiv)

variable {K : Type} [Field K] {d : ℕ} [Finite K]

theorem inner_split_twin (hK : ringChar K ≠ 2) (hd7 : 7 ≤ d)
    {R : GL (Fin d) K} (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) (hker : OKer (oQ R))
    {X : Type} [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (θ : GeneralizedFitting.subgroup X ≃* StatedProj (matrixDerived (oQ R)))
    {t : X} (hsurj : OSurjX θ t) (ht : orderOf t = 2) {g : similarityPairs (oQ R)}
    (htg : socleAction θ t = oκ _ g) {A' : GL (Fin d) K}
    (hA' : A' ∈ matrixIsometries (oQ R)) (hκ : oκ _ g = oκ _ (linPair A' hA'))
    (hAR : (A' : Matrix (Fin d) (Fin d) K)ᵀ * R * A' = R)
    (hA2 : (A' : Matrix (Fin d) (Fin d) K) * A' = 1) :
    oddCentralizerCore t = ⊥ ∨ (5 ≤ Nat.card K ∧ TwinSliceData (Ring.two_ne_zero hK) θ t) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hψ := socleAction_injective hsimple hnab θ
  set Rm := (R : Matrix (Fin d) (Fin d) K) with hRm
  obtain ⟨Am, hAm⟩ : ∃ Am : Matrix (Fin d) (Fin d) K, Am = A' := ⟨_, rfl⟩
  rw [← hAm] at hAR hA2
  have hbot : ∀ {T : Type} [Group T] {θ' : GeneralizedFitting.subgroup X ≃* T},
      oddCoreIn (socleAction θ').range (socleAction θ' t) = ⊥ → oddCentralizerCore t = ⊥ := by
    intro T _ θ' h
    have hψ' := socleAction_injective hsimple hnab θ'
    rw [← map_oddCentralizerCore_of_injective hψ'] at h
    exact (map_eq_bot_iff_of_injective _ hψ').1 h
  have htrans : ∀ (A'' : GL (Fin d) K) (hA'' : A'' ∈ matrixIsometries (oQ R)),
      oκ _ g = oκ _ (linPair A'' hA'') → ∀ {a b : ℕ} (hab : a + b = d)
      (c : Fin a ⊕ Fin b → Fin d → K),
      (∀ x, (A'' : Matrix (Fin d) (Fin d) K) *ᵥ c x =
        (if x.isLeft then (-1 : K) else 1) • c x) →
      (∀ x y, x ≠ y → c x ⬝ᵥ Rm *ᵥ c y = 0) → (∀ x, c x ⬝ᵥ Rm *ᵥ c x ≠ 0) →
      ∃ (hw : ∀ l, famW Rm hab c l ≠ 0) (S : GL (Fin d) K)
        (hS : ∀ v, oQ (diagGL hw) ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) =
          ((1 : Kˣ) : K) * oQ R v),
        OKer (oQ (diagGL hw)) ∧
        socleAction (θ.trans (oTransport S 1 hS)) t = oκ _ (sgnPair h2 hw (famJ hab)) ∧
        Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
          MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))) ∧
        (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
          MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))).range ≤
            (socleAction (θ.trans (oTransport S 1 hS))).range ∧
        OSurjCore (socleAction (θ.trans (oTransport S 1 hS))).range
          (oκ _ (sgnPair h2 hw (famJ hab))) := by
    intro A'' hA'' hκ'' a b hab c hcA horth hdiag
    obtain ⟨hw, S, hS, heq⟩ := exists_transport_of_family h2 hA'' hab c hcA horth hdiag
    have hψ't : socleAction (θ.trans (oTransport S 1 hS)) t =
        oκ _ (sgnPair h2 hw (famJ hab)) := by
      rw [socleAction_trans, htg, hκ'', oTransport_kappa, heq]
    exact ⟨hw, S, hS, hker.transport S 1 hS, hψ't,
      conj_injective_of_mulEquiv hsimple hnab (θ.trans (oTransport S 1 hS)),
      by rintro _ ⟨x, rfl⟩; exact conj_mem_range_socleAction _ x,
      ((hsurj.transport S 1 hS).core hsimple hnab).of_eq hψ't⟩
  have hslice : ∀ (A'' : GL (Fin d) K) (hA'' : A'' ∈ matrixIsometries (oQ R)),
      oκ _ g = oκ _ (linPair A'' hA'') →
      (A'' : Matrix (Fin d) (Fin d) K)ᵀ * Rm * A'' = Rm →
      (A'' : Matrix (Fin d) (Fin d) K) * A'' = 1 →
      Module.finrank K (eigM (A'' : Matrix (Fin d) (Fin d) K)) = 2 →
      oddCentralizerCore t = ⊥ ∨ (5 ≤ Nat.card K ∧ TwinSliceData h2 θ t) := by
    intro A'' hA'' hκ'' hAR'' hA2'' hM2''
    have hsum := finrank_eig_add h2 hA2''
    rw [hM2''] at hsum
    by_cases h3 : Nat.card K = 3
    ·
      left
      obtain ⟨hab, c, hcA, horth, hdiag, -, hNFc⟩ := exists_split_nf hK hR hAR'' hA2''
      obtain ⟨hw, S, hS, hker', hψ't, hinj', hB, hsurj'⟩ :=
        htrans A'' hA'' hκ'' hab c hcA horth hdiag
      refine hbot (θ' := θ.trans (oTransport S 1 hS)) ?_
      rw [hψ't]
      have hJcard : (famJ hab).card = 2 := by rw [card_famJ hab, hM2'']
      have hJccard : (famJ hab)ᶜ.card =
          Module.finrank K (eigP (A'' : Matrix (Fin d) (Fin d) K)) := by
        rw [Finset.card_compl, Fintype.card_fin, card_famJ hab]
        omega
      exact split_two_oddCoreIn_eq_bot_three_gen h3 hK hw hker' hsurj' hinj' hB hJcard
        ((hNFc (by omega)).blockOK (by omega) fun h => by omega)
    · right
      have hK5 : 5 ≤ Nat.card K := by
        have hodd := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK
        have h1 : 2 ≤ Nat.card K := Finite.one_lt_card
        obtain ⟨k, hk⟩ := hodd
        omega
      obtain ⟨hab, c, hcA, horth, hdiag, β, γ, hβ0, hγ0, hβ1, hγ1, h0, h1, h2', hr, hL⟩ :=
        exists_slice_nf_gen hK hR hAR'' hA2'' hM2'' (by omega)
      obtain ⟨hW, I₀, hI₀, hI₀3, hI₀w, hns⟩ := sliceW_of_nf_gen hab (by omega) hβ0 hβ1 hγ1
        h0 h1 h2' hr hL
      obtain ⟨hw, S, hS, hker', hψ't, hinj', hB, hsurj'⟩ :=
        htrans A'' hA'' hκ'' hab c hcA horth hdiag
      have hJ : famJ hab = jSet := by
        ext l
        rw [mem_famJ, mem_jSet]
      rw [hJ] at hψ't hsurj'
      have hJc3 : 3 ≤ (jSet : Finset (Fin d))ᶜ.card := by
        rw [Finset.card_compl, Fintype.card_fin, card_jSet (by omega)]
        omega
      refine ⟨hK5, by omega, _, hw, 1, β, hW, S, 1, hS, hker', hψ't, fun y hy => ?_⟩
      obtain ⟨g', rfl⟩ := hsurj' y hy
      obtain ⟨hτ, -, hiso⟩ := iso_of_mix hK hK5 hw hker' hinj' hB (Or.inr rfl) hJc3 hI₀ hI₀3
        hI₀w hns hy
      obtain ⟨R', hR', hRJ, hgR⟩ := exists_oIsoBlock_of_iso hK hw hker'
        (Finset.card_pos.1 (by omega)) hy hτ hiso
      exact ⟨R', hR', hRJ, hgR⟩
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
  left
  obtain ⟨hab, c, hcA, horth, hdiag, hNF, hNFc⟩ := exists_split_nf hK hR hAR hA2
  obtain ⟨hw, S, hS, hker', hψ't, hinj', hB, hsurj'⟩ :=
    htrans A' hA' hκ hab c (by rw [← hAm]; exact hcA) horth hdiag
  refine hbot (θ' := θ.trans (oTransport S 1 hS)) ?_
  rw [hψ't]
  have hJcard : (famJ hab).card = Module.finrank K (eigM Am) := card_famJ hab
  have hJccard : (famJ hab)ᶜ.card = Module.finrank K (eigP Am) := by
    rw [Finset.card_compl, Fintype.card_fin, hJcard]
    omega
  exact split_oddCoreIn_eq_bot_of_nf_gen hK hd7 hw hker' hsurj' hinj' hB
    (by omega) (by omega) (by omega) (by omega) (fun h3 => hNF (by omega))
    (fun h3 => hNFc (by omega))

end CFSG.ComponentClassification.Burgoyne.O
