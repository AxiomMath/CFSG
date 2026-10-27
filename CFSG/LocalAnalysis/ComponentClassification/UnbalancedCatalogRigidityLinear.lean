module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityCommon
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDescent

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearField

variable {K : Type*} [Field K] {n : ℕ}

@[expose] def subfieldSLIncl (n : ℕ) (σ : K ≃+* K) :
    SpecialLinearGroup (Fin n) (fixedField K σ) →* GL (Fin n) K :=
  SpecialLinearGroup.toGL.comp (SpecialLinearGroup.map (fixedField K σ).subtype)

@[expose] def subfieldConj (n : ℕ) (σ : K ≃+* K) :
    SpecialLinearGroup (Fin n) (fixedField K σ) →* MulAut (projectiveSL n K) :=
  (conjAut n K).comp (subfieldSLIncl n σ)

@[expose] def fixedSL (n : ℕ) (σ : K ≃+* K) : Subgroup (GL (Fin n) K) where
  carrier := {g | GeneralLinearGroup.det g = 1 ∧ GeneralLinearGroup.map (σ : K →+* K) g = g}
  mul_mem' {a b} ha hb := ⟨by rw [map_mul, ha.1, hb.1, one_mul], by rw [map_mul, ha.2, hb.2]⟩
  one_mem' := ⟨map_one _, map_one _⟩
  inv_mem' {a} ha := ⟨by rw [map_inv, ha.1, inv_one], by rw [map_inv, ha.2]⟩

theorem subfieldSLIncl_eq (σ : K ≃+* K) (B : SpecialLinearGroup (Fin n) (fixedField K σ)) :
    subfieldSLIncl n σ B =
      subfieldGLMap (Fin n) K (fixedField K σ) (SpecialLinearGroup.toGL B) :=
  GeneralLinearGroup.ext fun _ _ => rfl

theorem map_subfieldGLMap (σ : K ≃+* K) (B : GL (Fin n) (fixedField K σ)) :
    GeneralLinearGroup.map (σ : K →+* K) (subfieldGLMap (Fin n) K (fixedField K σ) B) =
      subfieldGLMap (Fin n) K (fixedField K σ) B :=
  GeneralLinearGroup.ext fun i j => fixedField_coe K σ (B i j)

theorem range_subfieldSLIncl (σ : K ≃+* K) : (subfieldSLIncl n σ).range = fixedSL n σ := by
  ext g
  constructor
  · rintro ⟨B, rfl⟩
    refine ⟨?_, ?_⟩
    · exact SpecialLinearGroup.coeToGL_det _
    · rw [subfieldSLIncl_eq, map_subfieldGLMap]
  · rintro ⟨hdet, hfix⟩
    obtain ⟨B, hB⟩ := exists_fixedField_GL (Fin n) K σ g fun i j => by
      have := congrArg (fun A : GL (Fin n) K => A i j) hfix
      simpa using this
    have hBdet : (B : Matrix (Fin n) (Fin n) (fixedField K σ)).det = 1 := by
      have h1 : GeneralLinearGroup.det (subfieldGLMap (Fin n) K (fixedField K σ) B) = 1 := by
        rw [hB, hdet]
      rw [GeneralLinearGroup.map_det] at h1
      have h2 := congrArg Units.val h1
      rw [Units.coe_map, Units.val_one] at h2
      rw [← GeneralLinearGroup.val_det_apply]
      exact Subtype.ext h2
    let B' : SpecialLinearGroup (Fin n) (fixedField K σ) := ⟨B, hBdet⟩
    refine ⟨B', ?_⟩
    rw [← hB]
    exact GeneralLinearGroup.ext fun _ _ => rfl

theorem range_subfieldConj (σ : K ≃+* K) :
    (subfieldConj n σ).range = (fixedSL n σ).map (conjAut n K) := by
  rw [subfieldConj, MonoidHom.range_comp, range_subfieldSLIncl]

theorem ker_subfieldConj [Finite K] (hn : 3 ≤ n) (σ : K ≃+* K) :
    (subfieldConj n σ).ker = scalars n (fixedField K σ) := by
  have : NeZero n := ⟨by omega⟩
  ext B
  rw [MonoidHom.mem_ker, mem_scalars]
  change conjAut n K (subfieldSLIncl n σ B) = 1 ↔ _
  rw [conjAut_eq_one_iff hn]
  constructor
  · rintro ⟨c, hc⟩
    rw [subfieldSLIncl_eq] at hc
    obtain ⟨b, hb⟩ := subfieldGLMap_scalar_reflect (Fin n) K (fixedField K σ)
      (SpecialLinearGroup.toGL B) c hc.symm
    refine ⟨b, ?_, ?_⟩
    · have h1 := congrArg GeneralLinearGroup.det hb
      rw [SpecialLinearGroup.coeToGL_det, GeneralLinearGroup.det_scalar, Fintype.card_fin] at h1
      exact h1.symm
    · have h2 := congrArg Units.val hb
      rw [SpecialLinearGroup.coe_GL_coe_matrix, GeneralLinearGroup.coe_scalar] at h2
      exact h2
  · rintro ⟨c, -, hB⟩
    refine ⟨Units.map (fixedField K σ).subtype.toMonoidHom c, ?_⟩
    refine GeneralLinearGroup.ext fun i j => ?_
    change _ = ((B i j : fixedField K σ) : K)
    rw [show B i j = (B : Matrix (Fin n) (Fin n) (fixedField K σ)) i j from rfl, hB]
    simp only [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply, Units.coe_map]
    split_ifs <;> simp

theorem linear_quadratic_field_full_centralizer_rigidity [Finite K] (σ : K ≃+* K)
    (hn : 3 ≤ n) :
    (subfieldConj n σ).ker = scalars n (fixedField K σ) ∧
      (∃ e : projectiveSL n (fixedField K σ) ≃* (subfieldConj n σ).range,
        ∀ B, (e (proj n (fixedField K σ) B) : MulAut (projectiveSL n K)) =
          subfieldConj n σ B) ∧
      (subfieldConj n σ).range ≤
        (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ∧
      (centralizer {fieldAut n K σ} : Set (MulAut (projectiveSL n K))) =
        {α | ∃ (B : GL (Fin n) (fixedField K σ)) (φ : K ≃+* K) (ε : ℕ), ε ≤ 1 ∧
          α = conjAut n K (subfieldGLMap (Fin n) K (fixedField K σ) B) * fieldAut n K φ *
            dualAut n K ^ ε} ∧
      (subfieldConj n σ).range ≤ centralizer {fieldAut n K σ} ∧
      ((subfieldConj n σ).range.subgroupOf (centralizer {fieldAut n K σ})).Normal ∧
      centralizer ((subfieldConj n σ).range : Set (MulAut (projectiveSL n K))) =
        zpowers (fieldAut n K σ) := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨-, -, hfc', -⟩ := standard_automorphism_transport (n := n) (K := K)
  have hfc : ∀ A : GL (Fin n) K, fieldAut n K σ * conjAut n K A =
      conjAut n K (GeneralLinearGroup.map (σ : K →+* K) A) * fieldAut n K σ :=
    fieldAut_mul_conjAut σ
  have hθf : ∀ φ : K ≃+* K, Commute (fieldAut n K σ) (fieldAut n K φ) :=
    fun φ => fieldAut_commute σ φ
  have hθd : Commute (fieldAut n K σ) (dualAut n K) := fieldAut_commute_dualAut σ
  set G : Set (GL (Fin n) K) := Set.range (subfieldGLMap (Fin n) K (fixedField K σ)) with hGdef
  have hG : ∀ A : GL (Fin n) K, Commute (fieldAut n K σ) (conjAut n K A) ↔
      ∃ B ∈ G, conjAut n K A = conjAut n K B := by
    intro A
    have hcomm : Commute (fieldAut n K σ) (conjAut n K A) ↔
        conjAut n K (GeneralLinearGroup.map (σ : K →+* K) A) = conjAut n K A := by
      change fieldAut n K σ * conjAut n K A = conjAut n K A * fieldAut n K σ ↔ _
      rw [hfc]
      exact mul_left_inj _
    rw [hcomm]
    constructor
    · intro h
      obtain ⟨c, hc⟩ := (conjAut_eq_conjAut_iff hn _ _).mp h
      have hfix : pglFieldAut (Fin n) K σ (ProjGenLinGroup.mk A) = ProjGenLinGroup.mk A := by
        change ProjGenLinGroup.mk (GeneralLinearGroup.map (σ : K →+* K) A) = _
        rw [hc, map_mul, ProjGenLinGroup.mk_scalar, mul_one]
      obtain ⟨B, hB⟩ := fixed_projective_exists_subfield_matrix (Fin n) K σ A hfix
      obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hB
      refine ⟨_, ⟨B, rfl⟩, ?_⟩
      rw [← hu, map_mul, conjAut_scalar, mul_one]
    · rintro ⟨_, ⟨B, rfl⟩, hAB⟩
      rw [← hfc' σ A, hAB, hfc' σ, map_subfieldGLMap]
  have hSG : ∀ B ∈ G, ∀ g ∈ fixedSL n σ, B * g * B⁻¹ ∈ fixedSL n σ := by
    rintro _ ⟨B, rfl⟩ g ⟨hg1, hg2⟩
    refine ⟨?_, ?_⟩
    · rw [map_mul, map_mul, map_inv, hg1, mul_one, mul_inv_cancel]
    · rw [map_mul, map_mul, map_inv, hg2, map_subfieldGLMap]
  have hSφ : ∀ φ : K ≃+* K, ∀ g ∈ fixedSL n σ,
      GeneralLinearGroup.map (φ : K →+* K) g ∈ fixedSL n σ := by
    rintro φ g ⟨hg1, hg2⟩
    refine ⟨?_, ?_⟩
    · rw [GeneralLinearGroup.map_det, hg1, map_one]
    · refine GeneralLinearGroup.ext fun i j => ?_
      have h1 := congrArg (fun A : GL (Fin n) K => A i j) hg2
      have h2 := DFunLike.congr_fun (ringAut_commute σ φ) (g i j)
      simp only [GeneralLinearGroup.map_apply, RingEquiv.coe_toRingHom] at h1 ⊢
      rw [RingAut.mul_apply, RingAut.mul_apply, h1] at h2
      exact h2
  have hSδ : ∀ g ∈ fixedSL n σ, GeneralLinearGroup.inverseTranspose g ∈ fixedSL n σ := by
    rintro g ⟨hg1, hg2⟩
    refine ⟨?_, ?_⟩
    · apply Units.ext
      rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_inverseTranspose,
        det_transpose, ← GeneralLinearGroup.val_det_apply, map_inv, hg1, inv_one]
    · rw [GeneralLinearGroup.map_inverseTranspose, hg2]
  have hNf : ∀ g ∈ fixedSL n σ, Commute (fieldAut n K σ) (conjAut n K g) := by
    rintro g ⟨-, hg2⟩
    change _ * _ = _ * _
    rw [hfc, hg2]
  have hrange := range_subfieldConj (n := n) σ
  have hfixT : ∀ {i j : Fin n} (hij : i ≠ j) (t : K), σ t = t →
      TauCeti.transvectionUnit hij t ∈ fixedSL n σ := by
    intro i j hij t ht
    refine ⟨TauCeti.det_transvectionUnit hij t, ?_⟩
    rw [map_transvectionUnit, RingEquiv.coe_toRingHom, ht]
  set i₀ : Fin n := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin n := ⟨1, by omega⟩ with hi₁
  set i₂ : Fin n := ⟨2, by omega⟩ with hi₂
  have h01 : i₀ ≠ i₁ := by simp [hi₀, hi₁, Fin.ext_iff]
  have h12 : i₁ ≠ i₂ := by simp [hi₁, hi₂, Fin.ext_iff]
  have h02 : i₀ ≠ i₂ := by simp [hi₀, hi₂, Fin.ext_iff]
  have hCN : centralizer ((subfieldConj n σ).range : Set (MulAut (projectiveSL n K))) =
      zpowers (fieldAut n K σ) := by
    rw [hrange]
    apply le_antisymm
    · intro α hα
      have hcent : ∀ g ∈ fixedSL n σ, α * conjAut n K g * α⁻¹ = conjAut n K g := by
        intro g hg
        have := mem_centralizer_iff.mp hα (conjAut n K g) (mem_map_of_mem _ hg)
        rw [← this, mul_inv_cancel_right]
      obtain ⟨A, φ, ε, hε, rfl⟩ := (automorphism_generation (K := K) hn).2 α
      rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
      · simp only [pow_zero, mul_one] at hcent ⊢
        have hAcomm : ∀ i j : Fin n, i ≠ j →
            Commute (single i j (1 : K)) (A : Matrix (Fin n) (Fin n) K) := by
          intro i j hij
          have h1 := hcent _ (hfixT hij 1 (map_one σ))
          rw [conj_conjAut_fieldAut, map_transvectionUnit, map_one] at h1
          have h2 := eq_of_conjAut_eq_of_unipotent hn
            (unipotent_conj (transvectionUnit_unipotent hij 1)) (transvectionUnit_unipotent hij 1)
            h1
          have h3 : A * TauCeti.transvectionUnit hij 1 = TauCeti.transvectionUnit hij 1 * A :=
            mul_inv_eq_iff_eq_mul.mp h2
          have h4 := congrArg Units.val h3
          rw [Units.val_mul, Units.val_mul, TauCeti.coe_transvectionUnit, Matrix.transvection,
            Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, add_right_inj] at h4
          exact h4.symm
        obtain ⟨r, hr⟩ := Matrix.mem_range_scalar_of_commute_single
          (fun i j hij => hAcomm i j hij)
        have hAc : A ∈ center (GL (Fin n) K) :=
          GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr ⟨r, hr⟩
        rw [GeneralLinearGroup.center_eq_range_scalar] at hAc
        obtain ⟨c, hc⟩ := hAc
        have hA1 : conjAut n K A = 1 := by
          rw [← hc]
          exact conjAut_scalar c
        rw [hA1, one_mul] at hcent ⊢
        have hφ : ∀ t, σ t = t → φ t = t := by
          intro t ht
          have h1 := hcent _ (hfixT h01 t ht)
          rw [hfc' φ, map_transvectionUnit] at h1
          have h2 := eq_of_conjAut_eq_of_unipotent hn (transvectionUnit_unipotent h01 _)
            (transvectionUnit_unipotent h01 t) h1
          exact TauCeti.transvectionUnit_injective h01 h2
        rw [← MonoidHom.map_zpowers]
        exact mem_map_of_mem _ (mem_zpowers_of_fixed hφ)
      · exfalso
        simp only [pow_one] at hcent
        have hrel : ∀ {i j : Fin n}, i ≠ j → (A : Matrix (Fin n) (Fin n) K) * single j i 1 =
            -(single i j 1 * (A : Matrix (Fin n) (Fin n) K)) := by
          intro i j hij
          have h1 := hcent _ (hfixT hij 1 (map_one σ))
          rw [conj_conjAut_fieldAut_dualAut, TauCeti.inverseTranspose_transvectionUnit,
            map_transvectionUnit, map_neg, map_one] at h1
          have h2 := eq_of_conjAut_eq_of_unipotent hn
            (unipotent_conj (transvectionUnit_unipotent hij.symm (-1)))
            (transvectionUnit_unipotent hij 1) h1
          have h3 : A * TauCeti.transvectionUnit hij.symm (-1) =
              TauCeti.transvectionUnit hij 1 * A :=
            mul_inv_eq_iff_eq_mul.mp h2
          have h4 := congrArg Units.val h3
          rw [Units.val_mul, Units.val_mul, TauCeti.coe_transvectionUnit,
            TauCeti.coe_transvectionUnit, Matrix.transvection, Matrix.transvection,
            Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, add_right_inj,
            ← single_neg, Matrix.mul_neg] at h4
          rw [← h4, neg_neg]
        have f1 : single i₀ i₁ (1 : K) * (A : Matrix (Fin n) (Fin n) K) =
            -((A : Matrix (Fin n) (Fin n) K) * single i₁ i₀ 1) :=
          (neg_eq_iff_eq_neg.mpr (hrel h01)).symm
        have f2 : single i₁ i₂ (1 : K) * (A : Matrix (Fin n) (Fin n) K) =
            -((A : Matrix (Fin n) (Fin n) K) * single i₂ i₁ 1) :=
          (neg_eq_iff_eq_neg.mpr (hrel h12)).symm
        have hzero : single i₀ i₂ (1 : K) * (A : Matrix (Fin n) (Fin n) K) = 0 := by
          calc single i₀ i₂ (1 : K) * (A : Matrix (Fin n) (Fin n) K)
              _ = single i₀ i₁ (1 : K) * (single i₁ i₂ 1 * (A : Matrix (Fin n) (Fin n) K)) := by
                rw [← Matrix.mul_assoc, single_mul_single_same, one_mul]
              _ = -((single i₀ i₁ (1 : K) * (A : Matrix (Fin n) (Fin n) K)) *
                  single i₂ i₁ 1) := by
                rw [f2, Matrix.mul_neg, ← Matrix.mul_assoc]
              _ = (A : Matrix (Fin n) (Fin n) K) * (single i₁ i₀ 1 * single i₂ i₁ 1) := by
                rw [f1, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
              _ = 0 := by
                rw [show single i₁ i₀ (1 : K) * single i₂ i₁ 1 = 0 by simp [h02],
                  Matrix.mul_zero]
        have hE : single i₀ i₂ (1 : K) = 0 := by
          have h1 : single i₀ i₂ (1 : K) * (A : Matrix (Fin n) (Fin n) K) *
              ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 0 := by
            rw [hzero, Matrix.zero_mul]
          rwa [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at h1
        have h1 := congrFun (congrFun hE i₀) i₂
        simp at h1
    · rw [zpowers_le, mem_centralizer_iff]
      rintro _ ⟨g, hg, rfl⟩
      exact (hNf g hg).eq.symm
  have hker := ker_subfieldConj hn σ
  refine ⟨hker, ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange (subfieldConj n σ)), fun B => rfl⟩, ?_, ?_, ?_, ?_, hCN⟩
  · rintro _ ⟨B, rfl⟩
    exact ⟨proj n K (SpecialLinearGroup.map (fixedField K σ).subtype B), (conjAut_toGL _).symm⟩
  · rw [centralizer_eq_of_conjAut_commute_iff hn hθf hθd G hG]
    ext α
    constructor
    · rintro ⟨_, ⟨B, rfl⟩, φ, ε, hε, h⟩
      exact ⟨B, φ, ε, hε, h⟩
    · rintro ⟨B, φ, ε, hε, h⟩
      exact ⟨_, ⟨B, rfl⟩, φ, ε, hε, h⟩
  · rw [hrange]
    rintro _ ⟨g, hg, rfl⟩
    exact mem_centralizer_singleton_iff.mpr (hNf g hg).eq.symm
  · rw [hrange]
    exact normal_of_conjAut_closed hn hθf hθd G hG (fixedSL n σ) hSG hSφ hSδ

end CFSG.ComponentClassification.UnbalancedCatalog
