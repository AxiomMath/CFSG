module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOFieldFrame
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOOddInner
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOForm
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSliceNF
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSplitCases
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUGraphCore
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUGraphDescent
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUInnerPaired
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation
  (field_involution_facts sq_val)
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.U (barEq barEq_apply)
open CFSG.ComponentClassification.Burgoyne.PSL (OrthNF diagGL coe_diagGL
  conj_injective_of_mulEquiv)

variable {K : Type} [Field K] {d : ℕ}

theorem exists_unitaryFieldData_of_involution [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) {σ : K ≃+* K} (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1) :
    ∃ e : ℕ, ∃ h : UnitaryFieldData p e K, σ = barEq h := by
  obtain ⟨hcard, huniq⟩ := field_involution_facts hp hf hK hσ2 hσ1
  set m := Nat.card {c : K // σ c = c} with hm
  have hdvd : m ∣ p ^ f := ⟨m, by rw [← hK, hcard, sq]⟩
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hfe : p ^ f = p ^ (2 * e) := by rw [← hK, hcard, he, ← pow_mul, mul_comm]
  have hf2 : f = 2 * e := Nat.pow_right_injective hp.two_le hfe
  have h : UnitaryFieldData p e K := ⟨hp, by omega, by rw [hK, hf2]⟩
  refine ⟨e, h, (huniq (barEq h) ?_ ?_).symm⟩
  · apply RingEquiv.ext
    intro x
    rw [pow_two]
    change barEq h (barEq h x) = x
    rw [barEq_apply, barEq_apply, h.bar_bar]
  · intro h1
    obtain ⟨c, hc⟩ := h.exists_bar_ne
    apply hc
    rw [← barEq_apply, h1]
    rfl

theorem colMat_gram (R : Matrix (Fin d) (Fin d) K) (c : Fin d → Fin d → K) (j k : Fin d) :
    ((Matrix.of fun i j => c j i)ᵀ * R * Matrix.of fun i j => c j i) j k =
      c j ⬝ᵥ R *ᵥ c k := by
  simp only [Matrix.mul_apply, transpose_apply, of_apply, dotProduct, mulVec, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

variable {p f : ℕ} (h : UnitaryFieldData p f K)

theorem exists_field_transport (hp2 : p ≠ 2) (h2 : (2 : K) ≠ 0) (hd3 : 3 ≤ d)
    {R : GL (Fin d) K} (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R)
    {g : similarityPairs (oQ R)} (hgσ : g.val.right = barEq h) {c : Kˣ}
    (hc : g.val.left * glFieldAut (Fin d) K g.val.right g.val.left =
      GeneralLinearGroup.scalar (Fin d) c) :
    ∃ (wF : Fin d → h.fixedField) (hwF : OrthNF wF) (S : GL (Fin d) K) (ν : Kˣ)
      (hS : ∀ v, oQ (diagGL (wK_ne_zero h hwF.1)) ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) =
        ν * oQ R v),
      oκ _ (transPair S ν hS g) = oκ _ (barPair h h2 hwF.1) := by
  set Rm := (R : Matrix (Fin d) (Fin d) K) with hRm
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin d) (Fin d) K, A = g.val.left := ⟨_, rfl⟩
  have hAdet : A.det ≠ 0 := by rw [hA]; exact (Matrix.isUnits_det_units _).ne_zero
  obtain ⟨μ, hμ⟩ := (mem_similarityPairs_oQ h2 R hR g.val).1 g.2
  rw [hgσ] at hμ
  have hμ' : Aᵀ * Rm * A = (μ : K) • Rm.map h.bar := by rw [hA]; exact hμ
  have hcA : A * A.map h.bar = (c : K) • 1 := by
    have e := congrArg Units.val hc
    rw [Units.val_mul, coe_glFieldAut, hgσ, GeneralLinearGroup.coe_scalar] at e
    rw [hA]
    change (g.val.left : Matrix (Fin d) (Fin d) K) *
      (g.val.left : Matrix (Fin d) (Fin d) K).map (barEq h) = _
    rw [e, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  obtain ⟨l, r, hl0, hr0, hA'2, hF⟩ := exists_field_descent h (by omega) hAdet hμ' c.ne_zero hcA
  obtain ⟨cv, wF, hNF, hcvτ, hgram⟩ := exists_field_frame h hp2 h2 hd3 hR hA'2 hr0 hF
  set H : Matrix (Fin d) (Fin d) K := Matrix.of fun i j => cv j i with hH
  have hHg : Hᵀ * Rm * H = r • diagonal (wK h wF) := by
    ext j k
    rw [hH, colMat_gram, hgram, Matrix.smul_apply, diagonal_apply, smul_eq_mul]
  have hdet : H.det ≠ 0 := by
    intro h0
    have e := congrArg Matrix.det hHg
    rw [det_mul, det_mul, det_transpose, h0, zero_mul, zero_mul, det_smul, det_diagonal] at e
    exact mul_ne_zero (pow_ne_zero _ hr0) (Finset.prod_ne_zero_iff.2 fun i _ =>
      wK_ne_zero h hNF.1 i) e.symm
  set Hg : GL (Fin d) K := Matrix.nonsingInvUnit H (isUnit_iff_ne_zero.2 hdet) with hHgdef
  have hHgv : ((Hg : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = H := rfl
  have hHHi : H * ((Hg⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
    rw [← hHgv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hHiH : ((Hg⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * H = 1 := by
    rw [← hHgv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hS : ∀ v, oQ (diagGL (wK_ne_zero h hNF.1))
      (((Hg⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v) =
        ((Units.mk0 r⁻¹ (inv_ne_zero hr0) : Kˣ) : K) * oQ R v := by
    intro v
    have hdiag : diagonal (wK h wF) = r⁻¹ • (Hᵀ * Rm * H) := by
      rw [hHg, smul_smul, inv_mul_cancel₀ hr0, one_smul]
    rw [oQ_apply, oQ_apply, coe_diagGL, hdiag, smul_mulVec, dotProduct_smul,
      dotProduct_transpose_mul_mul, mulVec_mulVec, hHHi, one_mulVec, Units.val_mk0, smul_eq_mul]
  refine ⟨wF, hNF, Hg⁻¹, Units.mk0 r⁻¹ (inv_ne_zero hr0), hS, ?_⟩
  refine oκ_eq_of_left_eq (c := Units.mk0 l hl0) (by rw [transPair_right, hgσ, barPair_right]) ?_
  rw [transPair_left, barPair_left, mul_one, hgσ, map_inv, inv_inv]
  apply Units.ext
  have hA'H : (l⁻¹ • A) * H.map h.bar = H := by
    ext i j
    have e := congrFun (hcvτ j) i
    rw [Matrix.mul_apply]
    change _ = cv j i
    rw [← e]
    simp only [mulVec, dotProduct, barV, hH, Matrix.map_apply, of_apply]
  have hAH : A * H.map h.bar = l • H := by
    conv_rhs => rw [← hA'H]
    rw [Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hl0, one_smul]
  rw [Units.val_mul, Units.val_mul, coe_glFieldAut, hHgv, GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Units.val_mk0, ← hA]
  change ((Hg⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * A * H.map h.bar = _
  rw [Matrix.mul_assoc, hAH, Matrix.mul_smul, hHiH, ← Matrix.smul_one_eq_diagonal]

theorem field_propAConclusion [Finite K] (hK : ringChar K ≠ 2) (hd5 : 5 ≤ d) {ℓ e : ℕ}
    (hℓ : ℓ.Prime) (he : 1 ≤ e) (hKc : Nat.card K = ℓ ^ e) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) (hker : OKer (oQ R))
    {X : Type} [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (θ : GeneralizedFitting.subgroup X ≃* StatedProj (matrixDerived (oQ R)))
    {t : X} (hsurj : OSurjX θ t) (ht : orderOf t = 2) {g : similarityPairs (oQ R)}
    (hg1 : g.val.right ≠ 1)
    (htg : socleAction θ t = oκ _ g) {Y : Subgroup X} (hY : Y ≠ ⊥)
    (hYO : Y ≤ oddCentralizerCore t) : PropAConclusion X t Y := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have : Fintype K := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hℓ2 : ℓ ≠ 2 := by rw [← ringChar.eq K ℓ]; exact hK
  have hgg : oκ (oQ R) (g * g) = 1 := by
    rw [map_mul, ← htg, ← map_mul, ← pow_two, ← ht, pow_orderOf_eq_one, map_one]
  obtain ⟨hσ2', c, hc⟩ := hker _ hgg
  have hσ2 : g.val.right ^ 2 = 1 := by rw [← (sq_val _ g).2]; exact hσ2'
  have hc' : g.val.left * glFieldAut (Fin d) K g.val.right g.val.left =
      GeneralLinearGroup.scalar (Fin d) c := by rw [← (sq_val _ g).1, hc]
  obtain ⟨e', hu, hσ⟩ := exists_unitaryFieldData_of_involution hℓ he hKc hσ2 hg1
  obtain ⟨wF, hwF, S, ν, hS, heq⟩ := exists_field_transport hu hℓ2 h2 (by omega) hR hσ hc'
  have ht' : socleAction (θ.trans (oTransport S ν hS)) t = oκ _ (barPair hu h2 hwF.1) := by
    rw [socleAction_trans, htg, oTransport_kappa, heq]
  refine propAConclusion_of_socle hsimple hnab (θ.trans (oTransport S ν hS)) hY hYO (Or.inl ?_)
  rw [ht']
  exact field_oddCoreIn_eq_bot hu hℓ2 h2 hd5 hwF (hker.transport S ν hS)
    (conj_injective_of_mulEquiv hsimple hnab (θ.trans (oTransport S ν hS)))
    (by rintro _ ⟨x, rfl⟩; exact conj_mem_range_socleAction _ x)
    (((hsurj.transport S ν hS).core hsimple hnab).of_eq ht')

end CFSG.ComponentClassification.Burgoyne.O
