module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePOmegaOdd
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBOTwin
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOShape
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Foundations
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBFinal
public import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation (sq_val)
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat
  conj_injective_of_mulEquiv eq_bot_of_oddCoreIn)

variable {K : Type} [Field K] {d : ℕ}

@[expose] def TwinSliceData (h2 : (2 : K) ≠ 0) {Q : QuadraticForm K (Fin d → K)} {X : Type}
    [Group X] (θ : GeneralizedFitting.subgroup X ≃* StatedProj (matrixDerived Q)) (t : X) :
    Prop :=
  ∃ (hd5 : 5 ≤ d) (w : Fin d → K) (hw : ∀ i, w i ≠ 0) (α a : K)
    (hW : OSliceW (by omega : 4 ≤ d) w α a) (S : GL (Fin d) K) (ν : Kˣ)
    (hS : ∀ v, oQ (diagGL hw) ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * Q v),
    OKer (oQ (diagGL hw)) ∧
      socleAction (θ.trans (oTransport S ν hS)) t = oκ _ (sgnPair h2 hw jSet) ∧
      ∀ y ∈ oddCoreIn (socleAction (θ.trans (oTransport S ν hS))).range
          (oκ _ (sgnPair h2 hw jSet)),
        ∃ (R' : GL (Fin d) K) (hR' : R' ∈ matrixIsometries (oQ (diagGL hw))),
          R' ∈ oIsoBlock K hw jSet ∧ y = oκ _ (linPair R' hR')

variable [Finite K]

theorem inner_odd_twin (hK : ringChar K ≠ 2) (hd7 : 7 ≤ d) (hdodd : Odd d)
    {R : GL (Fin d) K} (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) (hker : OKer (oQ R))
    {X : Type} [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (θ : GeneralizedFitting.subgroup X ≃* StatedProj (matrixDerived (oQ R)))
    {t : X} (hsurj : OSurjX θ t) (ht : orderOf t = 2) {g : similarityPairs (oQ R)}
    (hg1 : g.val.right = 1) (htg : socleAction θ t = oκ _ g) :
    oddCentralizerCore t = ⊥ ∨ (5 ≤ Nat.card K ∧ TwinSliceData (Ring.two_ne_zero hK) θ t) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hψ := socleAction_injective hsimple hnab θ
  set Rm := (R : Matrix (Fin d) (Fin d) K) with hRm
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
    obtain ⟨k, hk⟩ := hdodd
    obtain ⟨hab, c, hcA, horth, hdiag, α, β, hα, hβ, h0, h1, h2', h3, hr⟩ :=
      exists_slice_nf hK hR hAR'' hA2'' hM2'' (by omega) ⟨k - 1, by omega⟩
    obtain ⟨hW, hJc⟩ := sliceW_of_nf hab (by omega) hα hβ h0 h1 h2' h3 hr
    obtain ⟨hw, S, hS, hker', hψ't, hinj', hB, hsurj'⟩ :=
      htrans A'' hA'' hκ'' hab c hcA horth hdiag
    have hJ : famJ hab = jSet := by
      ext l
      rw [mem_famJ, mem_jSet]
    rw [hJ] at hψ't hsurj'
    have hJ2 : (jSet : Finset (Fin d)).card = 2 := by
      rw [show (jSet : Finset (Fin d)) = {⟨0, by omega⟩, ⟨1, by omega⟩} from by
        ext i
        simp only [mem_jSet, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
        omega]
      exact Finset.card_pair (by simp [Fin.ext_iff])
    have hJd : 2 * (jSet : Finset (Fin d)).card ≠ d := by omega
    have hodd : Odd (Nat.card K) := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK
    by_cases h3K : Nat.card K = 3
    · left
      refine hbot (θ' := θ.trans (oTransport S 1 hS)) ?_
      rw [hψ't]
      exact split_two_oddCoreIn_eq_bot_three h3K hK hw hker' hsurj' hinj' hB hJ2 hJd hJc
    · right
      have hK5 : 5 ≤ Nat.card K := by
        have h1 : 2 ≤ Nat.card K := Finite.one_lt_card
        obtain ⟨k, hk⟩ := hodd
        omega
      refine ⟨hK5, by omega, _, hw, α, β / α, hW, S, 1, hS, hker', hψ't, fun y hy => ?_⟩
      exact split_two_oddCoreIn hK hw hker' hsurj' hinj' hB hJd hJc hy
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
  have hA'c : (A' : Matrix (Fin d) (Fin d) K) = m⁻¹ • (g.val.left : Matrix (Fin d) (Fin d) K) := by
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
  obtain ⟨hw, S, hS, hker', hψ't, hinj', hB, hsurj'⟩ :=
    htrans A' hA' hκ hab c (by rw [← hAm]; exact hcA) horth hdiag
  left
  refine hbot (θ' := θ.trans (oTransport S 1 hS)) ?_
  rw [hψ't]
  have hJcard : (famJ hab).card = Module.finrank K (eigM Am) := card_famJ hab
  have hJccard : (famJ hab)ᶜ.card = Module.finrank K (eigP Am) := by
    rw [Finset.card_compl, Fintype.card_fin, hJcard]
    omega
  exact split_oddCoreIn_eq_bot_of_nf hK hd7 ⟨_, hdodd.choose_spec⟩ hw hker' hsurj' hinj' hB
    (by omega) (by omega) (by omega) (by omega) (fun h3 => hNF (by omega))
    (fun h3 => hNFc (by omega))


theorem field_odd_core_bot (hK : ringChar K ≠ 2) (hd5 : 5 ≤ d) {ℓ e : ℕ}
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

end CFSG.ComponentClassification.Burgoyne.O
