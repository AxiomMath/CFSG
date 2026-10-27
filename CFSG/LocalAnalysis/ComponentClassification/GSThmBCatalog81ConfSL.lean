module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4LayerC
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OutCard
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4CoverCore

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag CatFactsSp4
open CatalogueBSymplecticB CatalogueBAlternatingIsometry

namespace ConfP

theorem map_center_equiv {G H : Type*} [Group G] [Group H] (φ : G ≃* H) :
    (center G).map φ.toMonoidHom = center H := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_center_iff] at hx
    rw [mem_center_iff]
    intro h
    obtain ⟨g, rfl⟩ := φ.surjective h
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hx g]
  · intro hy
    refine ⟨φ.symm y, ?_, by simp⟩
    rw [SetLike.mem_coe, mem_center_iff]
    rw [mem_center_iff] at hy
    intro g
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy (φ g)]

theorem SL2_eq_one_or_neg_one {E : Type*} [Field E] (h2 : (2 : E) ≠ 0)
    {X : Matrix.SpecialLinearGroup (Fin 2) E} (hX : X * X = 1) : X = 1 ∨ X = -1 := by
  have hdet : (X : Matrix (Fin 2) (Fin 2) E).det = 1 := X.2
  rw [Matrix.det_fin_two] at hdet
  have hm : (X : Matrix (Fin 2) (Fin 2) E) * X = 1 := by
    have := congrArg (fun Y : Matrix.SpecialLinearGroup (Fin 2) E =>
      (Y : Matrix (Fin 2) (Fin 2) E)) hX
    simpa using this
  have e00 := congrFun (congrFun hm 0) 0
  have e01 := congrFun (congrFun hm 0) 1
  have e10 := congrFun (congrFun hm 1) 0
  have e11 := congrFun (congrFun hm 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e00 e01 e10 e11
  have hs : (X : Matrix (Fin 2) (Fin 2) E) 0 0 + (X : Matrix (Fin 2) (Fin 2) E) 1 1 ≠ 0 := by
    intro hs
    apply h2
    linear_combination -e00 - hdet + (X : Matrix (Fin 2) (Fin 2) E) 0 0 * hs
  have hb : (X : Matrix (Fin 2) (Fin 2) E) 0 1 = 0 := by
    have : (X : Matrix (Fin 2) (Fin 2) E) 0 1 *
        ((X : Matrix (Fin 2) (Fin 2) E) 0 0 + (X : Matrix (Fin 2) (Fin 2) E) 1 1) = 0 := by
      linear_combination e01
    exact (mul_eq_zero.mp this).resolve_right hs
  have hc : (X : Matrix (Fin 2) (Fin 2) E) 1 0 = 0 := by
    have : (X : Matrix (Fin 2) (Fin 2) E) 1 0 *
        ((X : Matrix (Fin 2) (Fin 2) E) 0 0 + (X : Matrix (Fin 2) (Fin 2) E) 1 1) = 0 := by
      linear_combination e10
    exact (mul_eq_zero.mp this).resolve_right hs
  have haa : (X : Matrix (Fin 2) (Fin 2) E) 0 0 * (X : Matrix (Fin 2) (Fin 2) E) 0 0 = 1 := by
    rw [hb] at e00
    linear_combination e00
  have had : (X : Matrix (Fin 2) (Fin 2) E) 0 0 * (X : Matrix (Fin 2) (Fin 2) E) 1 1 = 1 := by
    rw [hb] at hdet
    linear_combination hdet
  have hda : (X : Matrix (Fin 2) (Fin 2) E) 1 1 = (X : Matrix (Fin 2) (Fin 2) E) 0 0 := by
    linear_combination (X : Matrix (Fin 2) (Fin 2) E) 0 0 * had -
      (X : Matrix (Fin 2) (Fin 2) E) 1 1 * haa
  rcases mul_self_eq_one_iff.mp haa with ha1 | ha1
  · left
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, hda, ha1]
  · right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, hda, ha1]

variable {K : Type} [Field K]

theorem exists_fixOf_equiv_SL2 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (A : gsp 2 K) {d : K} (hd0 : d ≠ 0) (hdsq : ∀ l : K, l ^ 2 ≠ d)
    (hAA : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = d • 1)
    (hμ : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * formJ 2 K *
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = d • formJ 2 K) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = (p ^ f) ^ 2 ∧
      Nonempty (fixOf (conjSp 2 K A) ≃* Matrix.SpecialLinearGroup (Fin 2) E) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos f).ne')
  set Ag : LinearMap.GeneralLinearGroup K (Fin 2 ⊕ Fin 2 → K) :=
    LinearMap.GeneralLinearGroup.ofLinearEquiv (matrixLinIso (A : GL (Fin 2 ⊕ Fin 2) K))
    with hAgdef
  have hAg : ∀ v, (Ag : Module.End K (Fin 2 ⊕ Fin 2 → K)) v =
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v := fun v => rfl
  have hdim : Module.finrank K (Fin 2 ⊕ Fin 2 → K) = 2 * 2 := finrank_standard
  have hAns : ∀ c : K, (Ag : Module.End K (Fin 2 ⊕ Fin 2 → K)) ≠ c • 1 := by
    intro c hc
    apply hdsq c
    set e : Fin 2 ⊕ Fin 2 → K := Pi.single (Sum.inl 0) 1 with he
    have h1 : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ e =
        c • e := by
      have := LinearMap.congr_fun hc e
      rwa [hAg] at this
    have h2 : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
        (((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ e) =
        d • e := by rw [mulVec_mulVec, hAA, smul_mulVec, one_mulVec]
    rw [h1, mulVec_smul, h1, smul_smul] at h2
    have h3 := congrFun h2 (Sum.inl 0)
    simp only [he, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h3
    rw [sq]
    exact h3
  have hAA' : (Ag : Module.End K (Fin 2 ⊕ Fin 2 → K)) * (Ag : Module.End K (Fin 2 ⊕ Fin 2 → K)) =
      d • 1 := by
    apply LinearMap.ext
    intro v
    rw [Module.End.mul_apply, hAg, hAg, mulVec_mulVec, hAA, smul_mulVec, one_mulVec]
    rfl
  have hμ' : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ *
      formJ 2 K * ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((Units.mk0 d hd0 : Kˣ) : K) • formJ 2 K := by rw [Units.val_mk0]; exact hμ
  have hAμ : ∀ v w, pairedSympForm K 2 ((Ag : Module.End K (Fin 2 ⊕ Fin 2 → K)) v)
      ((Ag : Module.End K (Fin 2 ⊕ Fin 2 → K)) w) = d * pairedSympForm K 2 v w := fun v w =>
    matrix_similitude _ (Units.mk0 d hd0) hμ' v w
  obtain ⟨-, -, hnonsplit⟩ := UnitaryHigher.odd_symplectic_scalar_square_centralizer_structure
    hp hp2 hf hK (r := 2) (by norm_num) hdim SymplecticFlag.pairedSympForm_isAlt
    SymplecticFlag.pairedSympForm_nondegenerate hAns hd0 hAA' hAμ
  obtain ⟨-, hF, hcard, hfinrank, -, -, -, -, hpos, -⟩ := hnonsplit hdsq
  obtain ⟨BE, -, hBEalt, hBEnd, -, hiff⟩ := hpos (div_self hd0)
  let : Field (UnitaryHigher.scalarSquareField (Ag : Module.End K (Fin 2 ⊕ Fin 2 → K))) :=
    hF.toField
  have hEodd : Odd (Nat.card (UnitaryHigher.scalarSquareField
      (Ag : Module.End K (Fin 2 ⊕ Fin 2 → K)))) := by
    rw [hcard]
    exact ((hp.odd_of_ne_two hp2).pow).pow
  have := finite_of_odd_card hEodd
  have : Module.Finite (UnitaryHigher.scalarSquareField (Ag : Module.End K (Fin 2 ⊕ Fin 2 → K)))
      (Fin 2 ⊕ Fin 2 → K) :=
    CatalogueBOrthogonalScalarSquareField.evaluationModule_finite _
  let e := (fixOfConjSpEquiv A).trans (evaluationIsometryEquiv (pairedSympForm K 2) Ag
    (isometryGroup BE) (fun φ => ∀ v w, BE (φ v) (φ w) = BE v w) (mem_isometryGroup_iff BE) hiff)
  obtain ⟨e'⟩ := exists_planeIsometryEquivSL BE hBEalt hBEnd (by omega)
  exact ⟨_, inferInstance, inferInstance, hcard, ⟨e.trans e'⟩⟩

theorem negS_mem_fixOf (A : gsp 2 K) : negS K ∈ fixOf (conjSp 2 K A) :=
  conjSp_scalar A ((mem_spScalars_iff _).mpr (Or.inr (coe_negS (K := K))))

theorem negS_ne_one (h2 : (2 : K) ≠ 0) : negS K ≠ 1 := by
  intro h
  have := congrArg (fun x : StatedSp 2 K => ((x : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (Sum.inl 0) (Sum.inl 0)) h
  simp only [coe_negS] at this
  apply h2
  have h' : (-1 : K) = 1 := by simpa using this
  linear_combination -h'

theorem negS_mul_self : negS K * negS K = 1 := by
  apply sp_ext
  rw [Subgroup.coe_mul, Units.val_mul, coe_negS]
  simp

theorem fixOf_eq_one_or_negS {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (A : gsp 2 K) {d : K} (hd0 : d ≠ 0) (hdsq : ∀ l : K, l ^ 2 ≠ d)
    (hAA : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = d • 1)
    (hμ : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * formJ 2 K *
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = d • formJ 2 K)
    {T : StatedSp 2 K} (hT : T ∈ fixOf (conjSp 2 K A)) (hTT : T * T = 1) :
    T = 1 ∨ T = negS K := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos f).ne')
  obtain ⟨E, _, _, hE, ⟨φ⟩⟩ := exists_fixOf_equiv_SL2 hp hp2 hf hK A hd0 hdsq hAA hμ
  have hE2 : (2 : E) ≠ 0 :=
    two_ne_zero_of_odd_card (by rw [hE]; exact ((hp.odd_of_ne_two hp2).pow).pow)
  have hK2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card (odd_card_of_card_eq hp hp2 hK)
  have hnT := negS_mem_fixOf A
  have hφn : φ ⟨negS K, hnT⟩ = -1 := by
    rcases SL2_eq_one_or_neg_one hE2 (X := φ ⟨negS K, hnT⟩)
        (by rw [← map_mul, ← map_one φ]; congr 1; exact Subtype.ext negS_mul_self) with h | h
    · exfalso
      apply negS_ne_one hK2
      have := φ.injective (h.trans (map_one φ).symm)
      exact congrArg Subtype.val this
    · exact h
  rcases SL2_eq_one_or_neg_one hE2 (X := φ ⟨T, hT⟩)
      (by rw [← map_mul, ← map_one φ]; congr 1; exact Subtype.ext hTT) with h | h
  · left
    have := φ.injective (h.trans (map_one φ).symm)
    exact congrArg Subtype.val this
  · right
    have := φ.injective (h.trans hφn.symm)
    exact congrArg Subtype.val this

theorem exists_map_fixOf_equiv_PSL2 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (A : gsp 2 K) {d : K} (hd0 : d ≠ 0) (hdsq : ∀ l : K, l ^ 2 ≠ d)
    (hAA : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = d • 1)
    (hμ : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * formJ 2 K *
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = d • formJ 2 K) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = (p ^ f) ^ 2 ∧
      Nonempty (↥((fixOf (conjSp 2 K A)).map (proj 2 K)) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) E) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos f).ne')
  obtain ⟨E, _, _, hE, ⟨φ⟩⟩ := exists_fixOf_equiv_SL2 hp hp2 hf hK A hd0 hdsq hAA hμ
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card (odd_card_of_card_eq hp hp2 hK)
  have hZ : ∀ z ∈ spScalars 2 K, conjSp 2 K A z = z := fun z hz => conjSp_scalar A hz
  have hle : spScalars 2 K ≤ fixOf (conjSp 2 K A) := fun z hz => hZ z hz
  have hker : (fixProj (conjSp 2 K A)).ker = center (fixOf (conjSp 2 K A)) := by
    apply Subgroup.eq_of_le_of_card_ge (ker_fixProj_le_center _)
    rw [ker_fixProj, Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, card_spScalars h2]
    exact card_center_fixOf_nonsquare hp hp2 hf hK A hd0 hdsq hAA hμ
  refine ⟨E, inferInstance, inferInstance, hE, ⟨?_⟩⟩
  exact ((QuotientGroup.quotientKerEquivOfSurjective (fixProj (conjSp 2 K A))
      ((proj 2 K).subgroupMap_surjective (fixOf (conjSp 2 K A)))).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)).trans
    (QuotientGroup.congr _ _ φ (map_center_equiv φ))

theorem not_dvd_card_fixOf_typeI {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    [Finite K] (hK : Nat.card K = p ^ f) (Y : gsp 2 K) {d : K} (hd0 : d ≠ 0)
    (hYY : ((Y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((Y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = d • 1)
    (hμ : ((Y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * formJ 2 K *
      ((Y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        (-d) • formJ 2 K) :
    ¬ (p ^ f) ^ 2 * (((p ^ f) ^ 2) ^ 2 - 1) / 2 ∣ Nat.card (fixOf (conjAut 2 K Y)) := by
  intro hdvd
  have hodd : Odd (Nat.card K) := odd_card_of_card_eq hp hp2 hK
  have hqodd : Odd (p ^ f) := hK ▸ hodd
  have h2 := two_ne_zero_of_odd_card hodd
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hq2 : (p ^ f) ^ 2 ∣ (p ^ f) ^ 2 * (((p ^ f) ^ 2) ^ 2 - 1) / 2 := by
    obtain ⟨j, hj⟩ : 2 ∣ ((p ^ f) ^ 2) ^ 2 - 1 := by
      have h4 : Odd (((p ^ f) ^ 2) ^ 2) := (hqodd.pow).pow
      obtain ⟨r, hr⟩ := h4
      exact ⟨r, by omega⟩
    rw [hj, show (p ^ f) ^ 2 * (2 * j) = ((p ^ f) ^ 2 * j) * 2 by ring,
      Nat.mul_div_cancel _ two_pos]
    exact dvd_mul_right _ _
  obtain ⟨g, hg⟩ := exists_frame_typeI h2 hd0 hμ hYY
  have hGL : (Y : GL (Fin 2 ⊕ Fin 2) K) * (g : GL (Fin 2 ⊕ Fin 2) K) =
      (g : GL (Fin 2 ⊕ Fin 2) K) * ((aIgsp hd0 : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_aIgsp]
    exact hg
  have hfixmap := map_fixOf_of_comm (conj_inv_conjSp Y (aIgsp hd0) g hGL)
  have hcardY : Nat.card (fixOf (conjSp 2 K Y)) = Nat.card (fixI d hd0) := by
    rw [Nat.card_congr ((fixOf (conjSp 2 K Y)).equivMapOfInjective
      ((MulAut.conj g)⁻¹ : MulAut (StatedSp 2 K)).toMonoidHom
      ((MulAut.conj g)⁻¹ : MulAut (StatedSp 2 K)).injective).toEquiv, hfixmap]
  have hθα : ∀ x, conjAut 2 K Y (proj 2 K x) = proj 2 K (conjSp 2 K Y x) := fun x =>
    conjAut_proj Y x
  have hdv := card_fixOf_dvd h2 (conjSp 2 K Y) hθα
  obtain ⟨m, hm, hcm⟩ := card_fixI (p := p) h2 hd0
  rw [hcardY, hcm, hK] at hdv
  exact not_sq_dvd_typeI hp hf rfl hm ((hq2.trans hdvd).trans hdv)

end ConfP

end CFSG.ComponentClassification.GSThmB
