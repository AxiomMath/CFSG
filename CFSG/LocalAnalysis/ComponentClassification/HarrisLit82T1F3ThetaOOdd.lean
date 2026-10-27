module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePOmegaOdd
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3ThetaOTorus
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOShape
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation (sq_val)
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat
  conj_injective_of_mulEquiv eq_bot_of_oddCoreIn)
open CFSG.Blueprint

variable {K : Type} [Field K] {d : ℕ} [Finite K]

theorem field_oddCentralizerCore_eq_bot (hK : ringChar K ≠ 2) (hd5 : 5 ≤ d) {ℓ e : ℕ}
    (hℓ : ℓ.Prime) (he : 1 ≤ e) (hKc : Nat.card K = ℓ ^ e) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) (hker : OKer (oQ R))
    {X : Type} [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (θ : GeneralizedFitting.subgroup X ≃* StatedProj (matrixDerived (oQ R)))
    {t : X} (hsurj : OSurjX θ t) (ht : orderOf t = 2) {g : similarityPairs (oQ R)}
    (hg1 : g.val.right ≠ 1) (htg : socleAction θ t = oκ _ g) : oddCentralizerCore t = ⊥ :=
  CFSG.ComponentClassification.Burgoyne.C.field_oddCentralizerCore_eq_bot hK hd5 hℓ he hKc hR hker
    hsimple hnab θ hsurj ht hg1 htg

theorem inner_odd_pow_eq_one (hK : ringChar K ≠ 2) {ℓ e : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hKc : Nat.card K = ℓ ^ e) (hℓ2 : ℓ ≠ 2) (hd7 : 7 ≤ d) (hdodd : Odd d)
    {R : GL (Fin d) K} (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) (hker : OKer (oQ R))
    {X : Type} [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (θ : GeneralizedFitting.subgroup X ≃* StatedProj (matrixDerived (oQ R)))
    {t : X} (hsurj : OSurjX θ t) (ht : orderOf t = 2) {g : similarityPairs (oQ R)}
    (hg1 : g.val.right = 1) (htg : socleAction θ t = oκ _ g) {y : X}
    (hy : y ∈ oddCentralizerCore t) : y ^ (Nat.card K ^ 2 - 1) = 1 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hψ := socleAction_injective hsimple hnab θ
  set Rm := (R : Matrix (Fin d) (Fin d) K) with hRm
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
    obtain ⟨k, hk⟩ := hdodd
    obtain ⟨hab, c, hcA, horth, hdiag, α, β, hα, hβ, h0, h1, h2', h3, hr⟩ :=
      exists_slice_nf hK hR hAR'' hA2'' hM2'' (by omega) ⟨k - 1, by omega⟩
    obtain ⟨-, hJc⟩ := sliceW_of_nf hab (by omega) hα hβ h0 h1 h2' h3 hr
    refine htrans A'' hA'' hκ'' hab c hcA horth hdiag
      fun hw hker' hinj' B hB hsurj' y' hy' => ?_
    have hJ : famJ hab = jSet := by
      ext l
      rw [mem_famJ, mem_jSet]
    rw [hJ] at hsurj' hy'
    have hJ2 : (jSet : Finset (Fin d)).card = 2 := card_jSet (by omega)
    obtain ⟨R', hR', hRJ, rfl⟩ :=
      split_two_oddCoreIn hK hw hker' hsurj' hinj' hB (by omega) hJc hy'
    exact oκ_linPair_pow_card_sq_sub_one hKc hℓ2 hw hJ2 hR' hRJ
  have hκ1 : oκ (oQ R) g ≠ 1 := by
    intro h1
    rw [h1, ← map_one (socleAction θ)] at htg
    have := hψ htg
    rw [this, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hgg : oκ (oQ R) (g * g) = 1 := by
    rw [map_mul, ← htg, ← map_mul, ← pow_two, ← ht, pow_orderOf_eq_one, map_one]
  obtain ⟨-, c, hc⟩ := hker _ hgg
  have hc' : g.val.left * g.val.left = GeneralLinearGroup.scalar (Fin d) c := by
    rw [hc]
    change _ = g.val.left * glFieldAut (Fin d) K g.val.right g.val.left
    rw [hg1, map_one, MulAut.one_apply]
  obtain ⟨μ, hμ⟩ := (mem_similarityPairs_oQ h2 R hR g.val).1 g.2
  rw [hg1, show (R : Matrix (Fin d) (Fin d) K).map ⇑(1 : K ≃+* K) = R from by ext; rfl] at hμ
  obtain ⟨m, hm0, hA'R, hA'2⟩ := exists_isometric_involution hdodd hμ hc'
  obtain ⟨A', hA'def⟩ : ∃ A' : GL (Fin d) K,
      A' = GeneralLinearGroup.scalar (Fin d) (Units.mk0 m hm0)⁻¹ * g.val.left := ⟨_, rfl⟩
  have hA'c : (A' : Matrix (Fin d) (Fin d) K) =
      m⁻¹ • (g.val.left : Matrix (Fin d) (Fin d) K) := by
    rw [hA'def, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul, Units.val_inv_eq_inv_val,
      Units.val_mk0]
  obtain ⟨Am, hAm⟩ : ∃ Am : Matrix (Fin d) (Fin d) K, Am = A' := ⟨_, rfl⟩
  have hAR : Amᵀ * Rm * Am = Rm := by rw [hAm, hA'c]; exact hA'R
  have hA2 : Am * Am = 1 := by rw [hAm, hA'c]; exact hA'2
  have hA' : A' ∈ matrixIsometries (oQ R) :=
    (mem_matrixIsometries_oQ h2 R hR A').2 ((CatalogueBGraphForm.mem_isometryGroup _ _ _ _).2
      (by rw [← hAm]; exact hAR))
  have hκ : oκ _ g = oκ _ (linPair A' hA') := by
    refine oκ_eq_of_left_eq (c := Units.mk0 m hm0) (by rw [hg1, linPair_right]) ?_
    rw [linPair_left, hA'def, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
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
  rw [split_oddCoreIn_eq_bot_of_nf hK hd7 ⟨_, hdodd.choose_spec⟩ hw hker' hsurj' hinj' hB
    (by omega) (by omega) (by omega) (by omega) (fun h3 => hNF (by omega))
    (fun h3 => hNFc (by omega)), mem_bot] at hy'
  rw [hy', one_pow]

theorem pow_eq_one_of_mem_oddCentralizerCore_POmegaOdd (X : Type) [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a) {n p f : ℕ} (hp2 : p ≠ 2)
    (hL : LieModel (GeneralizedFitting.subgroup X) .POmegaOdd n p f) (t : X)
    (ht : orderOf t = 2) {y : X} (hy : y ∈ oddCentralizerCore t) :
    y ^ ((p ^ f) ^ 2 - 1) = 1 := by
  rcases hL with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  · have hmod := hc
    obtain ⟨⟨hp, hf, hn, -⟩, K, _, _, hKc, ⟨e⟩⟩ := hc
    have : Fintype K := Fintype.ofFinite K
    have : Fact p.Prime := ⟨hp⟩
    have : CharP K p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
    have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
    have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
    have hker₀ := oKer_coordinateOdd hmod K hKc e
    have hsurj₀ := oSurj_coordinateOdd hmod K hKc e
    obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadOdd n K)
      (regular_coordinateQuadOdd n K h2 hn).1
    have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n + 1)) K) : Matrix _ _ K) *ᵥ v) =
        ((1 : Kˣ) : K) * coordinateQuadOdd n K v := by
      intro v
      rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
    have hker := hker₀.transport 1 1 hS₁
    have hsurj := hsurj₀.transport 1 1 hS₁
    set θ := (coordinateOddWitnessEquiv K e).trans (oTransport 1 1 hS₁) with hθ
    obtain ⟨g, hg⟩ := hsurj (socleAction θ t)
    rw [← hKc]
    by_cases hσ : g.val.right = 1
    · exact inner_odd_pow_eq_one hK hKc hp2 (by omega) ⟨n, rfl⟩ hR hker hsimple hnab θ
        (hsurj.surjX θ t) ht hσ hg hy
    · rw [field_oddCentralizerCore_eq_bot hK (by omega) hp hf hKc hR hker hsimple hnab θ
        (hsurj.surjX θ t) ht hσ hg, mem_bot] at hy
      rw [hy, one_pow]
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)

end CFSG.ComponentClassification.Burgoyne.O
