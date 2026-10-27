module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotAutU
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotHR4LangPSL
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3EvenAut
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField
public import CFSG.LocalAnalysis.OddStandard.Seitz77Sylow
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag FieldFourCover

variable {K : Type} [Field K] [Finite K]

section RootElements

omit [Finite K]

theorem transvection_zero_one_eq_unipU (c : K) :
    SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c = unipU K c 0 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.transvection_coe, coe_unipU]

theorem transvection_zero_two_eq_unipU (c : K) :
    SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) c = unipU K 0 0 c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.transvection_coe, coe_unipU]

theorem transvection_one_two_eq_unipU (c : K) :
    SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) c = unipU K 0 c 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.transvection_coe, coe_unipU]

theorem proj_transvection_zero_one_mem_projRad (c : K) :
    proj 3 K (SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c) ∈
      projRad K 0 := by
  rw [transvection_zero_one_eq_unipU]
  exact mem_projRad_zero.2 ⟨c, 0, rfl⟩

theorem proj_transvection_one_two_mem_projRad (c : K) :
    proj 3 K (SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) c) ∈
      projRad K 1 := by
  rw [transvection_one_two_eq_unipU]
  exact mem_projRad_one.2 ⟨c, 0, rfl⟩

theorem proj_transvection_zero_two_mem_projRad (i : Fin 2) (c : K) :
    proj 3 K (SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) c) ∈
      projRad K i := by
  rw [transvection_zero_two_eq_unipU]
  fin_cases i
  · exact mem_projRad_zero.2 ⟨0, c, rfl⟩
  · exact mem_projRad_one.2 ⟨0, c, rfl⟩

theorem commute_single_of_fix (A : GL (Fin 3) K) (σ : K ≃+* K) {i j : Fin 3} (hij : i ≠ j)
    (h : (conjAut 3 K A * fieldAut 3 K σ) (proj 3 K (SpecialLinearGroup.transvection hij 1)) =
      proj 3 K (SpecialLinearGroup.transvection hij 1)) :
    Commute (single i j (1 : K)) (A : Matrix (Fin 3) (Fin 3) K) := by
  have h' := CFSG.SeitzReduction.LinearPilot.single_mul_eq_of_conjAut_mul_fieldAut_apply A σ hij
    1 1 h
  rwa [map_one] at h'

theorem single_mul_eq_neg_of_fix (A : GL (Fin 3) K) (σ : K ≃+* K) {i j : Fin 3} (hij : i ≠ j)
    (h : (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K)
        (proj 3 K (SpecialLinearGroup.transvection hij 1)) =
      proj 3 K (SpecialLinearGroup.transvection hij 1)) :
    single i j (1 : K) * (A : Matrix (Fin 3) (Fin 3) K) =
      -((A : Matrix (Fin 3) (Fin 3) K) * single j i 1) := by
  rw [CFSG.SeitzReduction.LinearPilot.single_mul_eq_of_conjAut_mul_fieldAut_mul_dualAut_apply A
    σ hij 1 1 h, map_one, ← single_neg, Matrix.mul_neg]

theorem false_of_single_mul_eq_neg_mul_single_two (A : GL (Fin 3) K)
    (h1 : single (1 : Fin 3) (2 : Fin 3) (1 : K) * (A : Matrix (Fin 3) (Fin 3) K) =
      -((A : Matrix (Fin 3) (Fin 3) K) * single 2 1 1))
    (h2 : single (0 : Fin 3) (2 : Fin 3) (1 : K) * (A : Matrix (Fin 3) (Fin 3) K) =
      -((A : Matrix (Fin 3) (Fin 3) K) * single 2 0 1)) : False := by
  have e02 := congrFun (congrFun h1 0) 1
  have e22 := congrFun (congrFun h1 2) 1
  have e12 := congrFun (congrFun h2 1) 0
  rw [single_mul_apply_of_ne (1 : K) (1 : Fin 3) (2 : Fin 3) 0 1 (by decide), Matrix.neg_apply,
    mul_single_apply_same, mul_one, zero_eq_neg] at e02
  rw [single_mul_apply_of_ne (1 : K) (1 : Fin 3) (2 : Fin 3) 2 1 (by decide), Matrix.neg_apply,
    mul_single_apply_same, mul_one, zero_eq_neg] at e22
  rw [single_mul_apply_of_ne (1 : K) (0 : Fin 3) (2 : Fin 3) 1 0 (by decide), Matrix.neg_apply,
    mul_single_apply_same, mul_one, zero_eq_neg] at e12
  apply Matrix.GeneralLinearGroup.det_ne_zero A
  refine Matrix.det_eq_zero_of_column_eq_zero 2 fun i => ?_
  fin_cases i
  · exact e02
  · exact e12
  · exact e22

theorem eq_one_of_single_mul_eq (A : GL (Fin 3) K) (σ : K ≃+* K)
    (h : ∀ c : K, single (0 : Fin 3) (2 : Fin 3) c * (A : Matrix (Fin 3) (Fin 3) K) =
      (A : Matrix (Fin 3) (Fin 3) K) * single 0 2 (σ c)) :
    σ = 1 := by
  have h1 : Commute (single (0 : Fin 3) (2 : Fin 3) (1 : K)) (A : Matrix (Fin 3) (Fin 3) K) := by
    have := h 1
    rwa [map_one] at this
  ext c
  have h2 : single (0 : Fin 3) (2 : Fin 3) c * (A : Matrix (Fin 3) (Fin 3) K) =
      (A : Matrix (Fin 3) (Fin 3) K) * single 0 2 c := by
    have hc : single (0 : Fin 3) (2 : Fin 3) c = c • single 0 2 (1 : K) := by
      rw [smul_single, smul_eq_mul, mul_one]
    rw [hc, Matrix.smul_mul, Matrix.mul_smul, h1.eq]
  have h3 := congrArg (fun M => ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M)
    ((h c).symm.trans h2)
  simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at h3
  have h4 := congrFun (congrFun h3 0) 2
  rw [single_apply_same, single_apply_same] at h4
  rw [RingAut.one_apply]
  exact h4

theorem conjAut_eq_conj_of_eq_smul (A : GL (Fin 3) K) (T : SpecialLinearGroup (Fin 3) K)
    {a : K} (ha : a ≠ 0)
    (h : (A : Matrix (Fin 3) (Fin 3) K) = a • (T : Matrix (Fin 3) (Fin 3) K)) :
    conjAut 3 K A = MulAut.conj (proj 3 K T) := by
  have hAT : A = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 a ha) *
      SpecialLinearGroup.toGL T := by
    apply Units.ext
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, SpecialLinearGroup.coe_GL_coe_matrix,
      Units.val_mk0, scalar_apply, ← smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
    exact h
  rw [hAT, map_mul, conjAut_scalar, one_mul, conjAut_toGL]

theorem conjAut_eq_conj_unipU (A : GL (Fin 3) K)
    (h10 : (A : Matrix (Fin 3) (Fin 3) K) 1 0 = 0) (h20 : (A : Matrix (Fin 3) (Fin 3) K) 2 0 = 0)
    (h21 : (A : Matrix (Fin 3) (Fin 3) K) 2 1 = 0)
    (h11 : (A : Matrix (Fin 3) (Fin 3) K) 1 1 = (A : Matrix (Fin 3) (Fin 3) K) 0 0)
    (h22 : (A : Matrix (Fin 3) (Fin 3) K) 2 2 = (A : Matrix (Fin 3) (Fin 3) K) 0 0) :
    conjAut 3 K A = MulAut.conj (proj 3 K (unipU K
      ((A : Matrix (Fin 3) (Fin 3) K) 0 1 / (A : Matrix (Fin 3) (Fin 3) K) 0 0)
      ((A : Matrix (Fin 3) (Fin 3) K) 1 2 / (A : Matrix (Fin 3) (Fin 3) K) 0 0)
      ((A : Matrix (Fin 3) (Fin 3) K) 0 2 / (A : Matrix (Fin 3) (Fin 3) K) 0 0))) := by
  have ha0 : (A : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := by
    intro h0
    apply Matrix.GeneralLinearGroup.det_ne_zero A
    rw [Matrix.det_fin_three, h10, h20, h21, h0]
    ring
  refine conjAut_eq_conj_of_eq_smul A _ ha0 ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_unipU, h10, h20, h21, h11, h22, mul_div_cancel₀ _ ha0]

end RootElements

section FixRadical

omit [Finite K] in
theorem exists_conj_eq_of_fix_projRad_zero (A : GL (Fin 3) K) (σ : K ≃+* K) {ε : ℕ}
    (hε : ε ≤ 1)
    (hα : ∀ x ∈ projRad K 0, (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K ^ ε) x = x) :
    ∃ r ∈ projRad K 0, conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K ^ ε = MulAut.conj r := by
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · rw [pow_zero, mul_one] at hα ⊢
    have hσ : σ = 1 := eq_one_of_single_mul_eq A σ fun c =>
      CFSG.SeitzReduction.LinearPilot.single_mul_eq_of_conjAut_mul_fieldAut_apply A σ h02 c c
        (hα _ (proj_transvection_zero_two_mem_projRad 0 c))
    subst hσ
    have hc01 := commute_single_of_fix A 1 h01 (hα _ (proj_transvection_zero_one_mem_projRad 1))
    have hc02 := commute_single_of_fix A 1 h02 (hα _ (proj_transvection_zero_two_mem_projRad 0 1))
    rw [map_one, mul_one, conjAut_eq_conj_unipU A (col_eq_zero_of_commute_single hc01 (by decide))
      (col_eq_zero_of_commute_single hc02 (by decide))
      (row_eq_zero_of_commute_single hc02 (by decide)) (diag_eq_of_commute_single hc01).symm
      (diag_eq_of_commute_single hc02).symm, row_eq_zero_of_commute_single hc01 (by decide),
      zero_div]
    exact ⟨_, mem_projRad_zero.2 ⟨_, _, rfl⟩, rfl⟩
  · exfalso
    rw [pow_one] at hα
    refine CFSG.SeitzReduction.LinearPilot.false_of_single_mul_eq_neg_mul_single (n := 3) le_rfl A
      fun j hj => ?_
    rcases hj with hj | hj
    · obtain rfl : j = 1 := Fin.ext hj
      exact single_mul_eq_neg_of_fix A σ h01 (hα _ (proj_transvection_zero_one_mem_projRad 1))
    · obtain rfl : j = 2 := Fin.ext hj
      exact single_mul_eq_neg_of_fix A σ h02 (hα _ (proj_transvection_zero_two_mem_projRad 0 1))

omit [Finite K] in
theorem exists_conj_eq_of_fix_projRad_one (A : GL (Fin 3) K) (σ : K ≃+* K) {ε : ℕ}
    (hε : ε ≤ 1)
    (hα : ∀ x ∈ projRad K 1, (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K ^ ε) x = x) :
    ∃ r ∈ projRad K 1, conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K ^ ε = MulAut.conj r := by
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · rw [pow_zero, mul_one] at hα ⊢
    have hσ : σ = 1 := eq_one_of_single_mul_eq A σ fun c =>
      CFSG.SeitzReduction.LinearPilot.single_mul_eq_of_conjAut_mul_fieldAut_apply A σ h02 c c
        (hα _ (proj_transvection_zero_two_mem_projRad 1 c))
    subst hσ
    have hc12 := commute_single_of_fix A 1 h12 (hα _ (proj_transvection_one_two_mem_projRad 1))
    have hc02 := commute_single_of_fix A 1 h02 (hα _ (proj_transvection_zero_two_mem_projRad 1 1))
    rw [map_one, mul_one, conjAut_eq_conj_unipU A (col_eq_zero_of_commute_single hc02 (by decide))
      (col_eq_zero_of_commute_single hc02 (by decide))
      (row_eq_zero_of_commute_single hc02 (by decide))
      ((diag_eq_of_commute_single hc12).trans (diag_eq_of_commute_single hc02).symm)
      (diag_eq_of_commute_single hc02).symm, col_eq_zero_of_commute_single hc12 (by decide),
      zero_div]
    exact ⟨_, mem_projRad_one.2 ⟨_, _, rfl⟩, rfl⟩
  · rw [pow_one] at hα
    exact (false_of_single_mul_eq_neg_mul_single_two A
      (single_mul_eq_neg_of_fix A σ h12 (hα _ (proj_transvection_one_two_mem_projRad 1)))
      (single_mul_eq_neg_of_fix A σ h02 (hα _ (proj_transvection_zero_two_mem_projRad 1 1)))).elim

theorem exists_conj_eq_of_fix_projRad (i : Fin 2) (α : MulAut (projectiveSL 3 K))
    (hα : ∀ x ∈ projRad K i, α x = x) : ∃ r ∈ projRad K i, α = MulAut.conj r := by
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (K := K) (n := 3) le_rfl).2 α
  fin_cases i
  · exact exists_conj_eq_of_fix_projRad_zero A σ hε hα
  · exact exists_conj_eq_of_fix_projRad_one A σ hε hα

end FixRadical


theorem isLangSurjective_of_not_mem_range {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {y : MulAut (projectiveSL 3 K)} (hy : y ^ 2 = 1)
    (hout : y ∉ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range) :
    CFSG.SeitzReduction.LinearPilot.IsLangSurjective y := by
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (K := K) (n := 3) le_rfl).2 y
  refine CFSG.SeitzReduction.LinearPilot.isLangSurjective_of_not_inner_of_not_even_graph hf hK
    le_rfl A σ ε hε hy ?_ fun h => absurd h.2.2 (by decide)
  rintro ⟨rfl, rfl⟩
  rw [pow_zero, mul_one, map_one, mul_one] at hy hout
  exact hout (CFSG.ComponentClassification.RankTwoL3Even.mem_inner_of_mem_linearAutGroup
    (conjAut_mem_linearAutGroup A) (k := 1) hy)

section Generic

open CFSG.ComponentClassification.RankTwoHypIIY

variable {W : Type*} [Group W]

theorem exists_perfect_of_isSimpleGroup {X L : Subgroup W} {t : W} (htX : t ∉ X)
    (ht2 : t ^ 2 = 1) (hLX : L ≤ X) (hLt : L ≤ centralizer ({t} : Set W)) (hL : IsSimpleGroup L)
    {x : W} (hx : x ∈ L) (hx1 : x ≠ 1) (hx2 : x ^ 2 = 1)
    (hC : centralizer ({t} : Set W) ⊓ centralizer (L : Set W) ≤ zpowers t) :
    ∃ L : Subgroup W, L ≤ X ∧ L ≤ centralizer ({t} : Set W) ∧ ⁅L, L⁆ = L ∧
      ∃ c ∈ L, orderOf c = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨L, hLX, hLt, commutator_eq_self_of_isSimpleGroup hL fun hcomm => ?_, x, hx,
    orderOf_eq_prime hx2 hx1⟩
  have hxL : x ∈ centralizer (L : Set W) := mem_centralizer_iff.2 fun l hl =>
    congrArg Subtype.val (hcomm ⟨l, hl⟩ ⟨x, hx⟩)
  rcases eq_one_or_eq_of_mem_zpowers ht2 (hC ⟨hLt hx, hxL⟩) with h | h
  · exact hx1 h
  · exact htX (h ▸ hLX hx)

theorem exists_perfect_conj {X : Subgroup W} (hX : X.Normal) {t₀ : W} (w : W)
    (h : ∃ L : Subgroup W, L ≤ X ∧ L ≤ centralizer ({t₀} : Set W) ∧ ⁅L, L⁆ = L ∧
      ∃ c ∈ L, orderOf c = 2) :
    ∃ L : Subgroup W, L ≤ X ∧ L ≤ centralizer ({w * t₀ * w⁻¹} : Set W) ∧ ⁅L, L⁆ = L ∧
      ∃ c ∈ L, orderOf c = 2 := by
  obtain ⟨L, hLX, hLt, hLp, c, hc, hc2⟩ := h
  refine ⟨L.map (MulAut.conj w).toMonoidHom, ?_, ?_, ?_, MulAut.conj w c, ⟨c, hc, rfl⟩, ?_⟩
  · rintro _ ⟨l, hl, rfl⟩
    exact hX.conj_mem l (hLX hl) w
  · rintro _ ⟨l, hl, rfl⟩
    have hl := hLt hl
    rw [mem_centralizer_singleton_iff] at hl ⊢
    change w * l * w⁻¹ * (w * t₀ * w⁻¹) = w * t₀ * w⁻¹ * (w * l * w⁻¹)
    calc w * l * w⁻¹ * (w * t₀ * w⁻¹) = w * (l * t₀) * w⁻¹ := by group
      _ = w * (t₀ * l) * w⁻¹ := by rw [hl]
      _ = w * t₀ * w⁻¹ * (w * l * w⁻¹) := by group
  · rw [← map_commutator, hLp]
  · rw [MulEquiv.orderOf_eq, hc2]

end Generic

section Canonical

open CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoHypIIL3
  CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.CatalogueBHigherLinearField

theorem exists_perfect_fieldAut [CharP K 2] (σ : K ≃+* K)
    (hX : fieldAut 3 K σ ∉
      (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range)
    (h2 : fieldAut 3 K σ ^ 2 = 1) :
    ∃ L : Subgroup (MulAut (projectiveSL 3 K)),
      L ≤ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range ∧
      L ≤ centralizer {fieldAut 3 K σ} ∧ ⁅L, L⁆ = L ∧ ∃ c ∈ L, orderOf c = 2 := by
  obtain ⟨-, ⟨e, -⟩, hinn, -, hcent, -, hC⟩ :=
    linear_quadratic_field_full_centralizer_rigidity (n := 3) σ le_rfl
  have := isSimpleGroup_projectiveSL_three (fixedField K σ)
  refine exists_perfect_of_isSimpleGroup hX h2 hinn hcent e.symm.isSimpleGroup ?_
    conjAut_swapGL_ne_one conjAut_swapGL_sq ?_
  · rw [range_subfieldConj]
    refine ⟨swapGL K, ⟨?_, ?_⟩, rfl⟩
    · exact Units.ext (by rw [GeneralLinearGroup.val_det_apply, coe_swapGL, det_swapMat]; rfl)
    · exact Units.ext (swapMat_map _)
  · rw [hC]
    exact inf_le_right

theorem exists_perfect_dualAut {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hX : dualAut 3 K ∉
      (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range) :
    ∃ L : Subgroup (MulAut (projectiveSL 3 K)),
      L ≤ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range ∧
      L ≤ centralizer {dualAut 3 K} ∧ ⁅L, L⁆ = L ∧ ∃ c ∈ L, orderOf c = 2 := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  obtain ⟨hinj, hinn, hβ2, -, hcent, -, hrest⟩ :=
    even_linear_canonical_graph_symplectic_centralizers (n := 3) (by omega) hK le_rfl 1
      (Or.inl rfl)
  obtain ⟨hC, -⟩ := hrest (Or.inr ⟨rfl, by decide⟩)
  have hβ : conjAut 3 K 1 * dualAut 3 K = dualAut 3 K := by rw [map_one, one_mul]
  rw [hβ] at hβ2 hcent hC
  set O := FourGroupEvenCanonical.matrixIsometryGroup
    ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hO
  have hNO : ((conjAut 3 K).comp O.subtype).range = O.map (conjAut 3 K) := by
    rw [MonoidHom.range_comp, range_subtype]
  obtain ⟨eSL⟩ := nonempty_matrixIsometryGroup_one_mulEquiv_SL2 (K := K)
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have := isSimpleGroup_SL2 h4
  have hsimple : IsSimpleGroup (O.map (conjAut 3 K)) :=
    ((MulEquiv.subgroupCongr hNO).symm.trans
      ((MonoidHom.ofInjective hinj).symm.trans eSL)).isSimpleGroup
  refine exists_perfect_of_isSimpleGroup hX hβ2 hinn hcent hsimple (mem_map_of_mem _ ?_)
    conjAut_swapGL_ne_one conjAut_swapGL_sq hC.le
  rw [hO, FourGroupEvenCanonical.mem_matrixIsometryGroup, Units.val_one, Matrix.mul_one,
    coe_swapGL, swapMat_transpose, swapMat_mul_self]

omit [Finite K] in
theorem exists_perfect_graphField {e : ℕ} (h : UnitaryFieldData 2 e K) (he : 2 ≤ e)
    (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x)
    (hX : fieldAut 3 K σ * dualAut 3 K ∉
      (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range)
    (h2 : (fieldAut 3 K σ * dualAut 3 K) ^ 2 = 1) :
    ∃ L : Subgroup (MulAut (projectiveSL 3 K)),
      L ≤ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range ∧
      L ≤ centralizer {fieldAut 3 K σ * dualAut 3 K} ∧ ⁅L, L⁆ = L ∧ ∃ c ∈ L, orderOf c = 2 := by
  have := h.finite
  have : CharP K 2 := h.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨ι, -⟩, hinn, -, hcent, -, hC⟩ :=
    linear_graph_field_full_centralizer_rigidity h (n := 3) le_rfl σ hσ
  have hq : ((3 : ℕ), 2 ^ e) ≠ (3, 2) := by
    intro hq
    have h2e : 2 ^ e = 2 ^ 1 := by simpa using congrArg Prod.snd hq
    have := Nat.pow_right_injective le_rfl h2e
    omega
  have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 e
    (by rw [h.card, ← pow_mul, mul_comm]) 3 le_rfl hq
  have hsimple := (ι.symm.trans
    (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv h (by norm_num))).isSimpleGroup
  refine exists_perfect_of_isSimpleGroup hX h2 hinn hcent hsimple (mem_map_of_mem _ ?_)
    conjAut_swapGL_ne_one conjAut_swapGL_sq ?_
  · rw [CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h, coe_swapGL, det_swapMat,
      swapMat_map, swapMat_transpose, swapMat_mul_self]
    exact ⟨rfl, rfl⟩
  · rw [hC]
    exact inf_le_right

end Canonical

section Outer

open CFSG.ComponentClassification

theorem exists_perfect_inner_of_not_mem {m : ℕ} (hm : 3 ≤ m) (hK : Nat.card K = 2 ^ m)
    {t : MulAut (projectiveSL 3 K)}
    (htX : t ∉ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range)
    (ht2 : t ^ 2 = 1) :
    ∃ L : Subgroup (MulAut (projectiveSL 3 K)),
      L ≤ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range ∧
      L ≤ centralizer {t} ∧ ⁅L, L⁆ = L ∧ ∃ c ∈ L, orderOf c = 2 := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  set X := (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range
  have hXn : X.Normal := ⟨fun _ ⟨x, hx⟩ w =>
    ⟨w x, by rw [← hx, SeitzReduction.LinearPilot.mulAut_mul_conj_mul_inv_eq_conj]⟩⟩
  have hconj : ∀ {t' w t₀ : MulAut (projectiveSL 3 K)}, t' ∉ X → t' ^ 2 = 1 →
      t' = w * t₀ * w⁻¹ → t₀ ∉ X ∧ t₀ ^ 2 = 1 := by
    intro t' w t₀ h1 h2 h
    subst h
    refine ⟨fun h0 => h1 (hXn.conj_mem t₀ h0 w), ?_⟩
    rwa [conj_pow, conj_eq_one_iff] at h2
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (K := K) (n := 3) le_rfl).2 t
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  ·
    rw [pow_zero, mul_one] at htX ht2 ⊢
    by_cases hσ : σ = 1
    ·
      exfalso
      subst hσ
      rw [map_one, mul_one] at htX ht2
      exact htX (RankTwoL3Even.mem_inner_of_mem_linearAutGroup (conjAut_mem_linearAutGroup A)
        (k := 1) ht2)
    ·
      obtain ⟨-, -, H, hH⟩ :=
        even_linear_field_involution_descent (n := 3) (by omega) hK le_rfl A σ hσ ht2
      obtain ⟨h0X, h02⟩ := hconj htX ht2 hH
      rw [hH]
      exact exists_perfect_conj hXn _ (exists_perfect_fieldAut σ h0X h02)
  ·
    rw [pow_one] at htX ht2 ⊢
    by_cases hσ : σ = 1
    ·
      subst hσ
      rw [map_one, mul_one] at htX ht2 ⊢
      obtain ⟨-, ⟨H, C, -, hH, hC⟩, -⟩ :=
        UnitaryHigher.even_linear_pure_graph_involution_normal_forms (n := 3) (by omega) hK
          le_rfl A ht2
      have hC1 : C = 1 := by
        rcases hC with ⟨hC1, -⟩ | ⟨r, hr, -⟩
        · exact Units.ext hC1
        · omega
      subst hC1
      rw [map_one, one_mul] at hH
      obtain ⟨h0X, -⟩ := hconj htX ht2 hH
      rw [hH]
      exact exists_perfect_conj hXn _ (exists_perfect_dualAut (by omega) hK h0X)
    ·
      obtain ⟨⟨e, he⟩, hσx, H, hH⟩ :=
        UnitaryHigher.linear_graph_field_involution_descent Nat.prime_two (by omega) hK le_rfl
          A σ hσ ht2
      have hud : UnitaryFieldData 2 e K := ⟨Nat.prime_two, by omega, by rw [hK, he, two_mul]⟩
      have hσbar : ∀ x, σ x = hud.bar x := fun x => by
        rw [hσx, UnitaryFieldData.bar_apply, show m / 2 = e by omega]
      obtain ⟨h0X, h02⟩ := hconj htX ht2 hH
      rw [hH]
      exact exists_perfect_conj hXn _ (exists_perfect_graphField hud (by omega) σ hσbar h0X h02)

theorem exists_perfect_of_not_mem_range {f : ℕ} (hf : 3 ≤ f) (hK : Nat.card K = 2 ^ f)
    {y : MulAut (projectiveSL 3 K)} (hy : y ^ 2 = 1)
    (hout : y ∉ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range) :
    ∃ D : Subgroup (projectiveSL 3 K), (∀ a ∈ D, y a = a) ∧ ⁅D, D⁆ = D ∧
      ∃ c ∈ D, orderOf c = 2 := by
  obtain ⟨L, hLX, hLy, hLp, c, hcL, hc2⟩ := exists_perfect_inner_of_not_mem hf hK hout hy
  have hinj := RankTwoL3Even.conj_injective_projectiveSL (F := K)
  set D := L.comap (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)) with hD
  have hDL : D.map (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)) = L :=
    map_comap_eq_self hLX
  refine ⟨D, fun a ha => hinj ?_, map_injective hinj ?_, ?_⟩
  · have h := mem_centralizer_singleton_iff.mp (hLy ha)
    rw [← SeitzReduction.LinearPilot.mulAut_mul_conj_mul_inv_eq_conj, ← h, mul_inv_cancel_right]
  · rw [map_commutator, hDL, hLp]
  · obtain ⟨c', rfl⟩ := hLX hcL
    exact ⟨c', hcL, by rw [← orderOf_injective _ hinj, hc2]⟩

end Outer

theorem le_range_conj_of_commutator_eq {D : Subgroup (MulAut (projectiveSL 3 K))}
    (hD : ⁅D, D⁆ = D) :
    D ≤ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := by
  have h := (standard_outer_quotients (K := K) (n := 3)).2.2.2.2.2.2.2.2.2
  rw [(automorphism_generation (K := K) (n := 3) le_rfl).1] at h
  have h1 : D ≤ ⁅(⊤ : Subgroup (MulAut (projectiveSL 3 K))), ⊤⁆ :=
    hD ▸ commutator_mono le_top le_top
  have h2 : D ≤ ⁅⁅(⊤ : Subgroup (MulAut (projectiveSL 3 K))), ⊤⁆, ⁅⊤, ⊤⁆⁆ :=
    calc D = ⁅D, D⁆ := hD.symm
      _ ≤ _ := commutator_mono h1 h1
  calc D = ⁅D, D⁆ := hD.symm
    _ ≤ _ := commutator_mono h2 h2
    _ ≤ _ := h

section F7

omit [Finite K] in
theorem eq_zero_of_independent {p q : K × K} (hd : p.1 * q.2 - q.1 * p.2 ≠ 0) {x y : K}
    (hp : x * p.1 + y * p.2 = 0) (hq : x * q.1 + y * q.2 = 0) : x = 0 ∧ y = 0 := by
  have hx : x * (p.1 * q.2 - q.1 * p.2) = 0 := by linear_combination q.2 * hp - p.2 * hq
  have hy : y * (p.1 * q.2 - q.1 * p.2) = 0 := by linear_combination p.1 * hq - q.1 * hp
  exact ⟨(mul_eq_zero.1 hx).resolve_right hd, (mul_eq_zero.1 hy).resolve_right hd⟩

theorem exists_independent_of_card_lt {S : Set (K × K)} (h : Nat.card K < Nat.card S) :
    ∃ p ∈ S, ∃ q ∈ S, p.1 * q.2 - q.1 * p.2 ≠ 0 := by
  by_contra hcon
  push Not at hcon
  refine absurd h (not_lt.2 ?_)
  by_cases h0 : ∃ p ∈ S, p.1 ≠ 0
  · obtain ⟨p, hp, hp1⟩ := h0
    refine Nat.card_le_card_of_injective (fun r : S => (r : K × K).1) ?_
    rintro ⟨r, hr⟩ ⟨s, hs⟩ hrs
    simp only at hrs
    have e1 := hcon p hp r hr
    have e2 := hcon p hp s hs
    have h2 : p.1 * (r.2 - s.2) = 0 := by rw [hrs] at e1; linear_combination e1 - e2
    have h3 : r.2 = s.2 := sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left hp1)
    exact Subtype.ext (Prod.ext hrs h3)
  · push Not at h0
    refine Nat.card_le_card_of_injective (fun r : S => (r : K × K).2) ?_
    rintro ⟨r, hr⟩ ⟨s, hs⟩ hrs
    exact Subtype.ext (Prod.ext ((h0 r hr).trans (h0 s hs).symm) hrs)

theorem card_fix_mul_card_fix_le {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) {σ : K ≃+* K}
    (hσ : σ ≠ 1) :
    Nat.card {t : K // σ t = t} * Nat.card {t : K // σ t = t} ≤ Nat.card K := by
  obtain ⟨-, -, -, -, -, hA⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two hf hK
  obtain ⟨hdvd, S, hS, hcard⟩ := hA (Subgroup.zpowers σ)
  rw [Nat.card_zpowers] at hdvd hcard
  have hh : 2 ≤ orderOf σ := by
    have h0 : orderOf σ ≠ 0 := fun h => by rw [h, zero_dvd_iff] at hdvd; omega
    have h1 : orderOf σ ≠ 1 := fun h => hσ (orderOf_eq_one_iff.1 h)
    omega
  have hle : Nat.card {t : K // σ t = t} ≤ Nat.card S := by
    refine Nat.card_le_card_of_injective (fun t => ⟨t.1, ?_⟩) ?_
    · rw [← SetLike.mem_coe, hS]
      intro τ hτ
      have hst : Subgroup.zpowers σ ≤ MulAction.stabilizer (K ≃+* K) t.1 :=
        Subgroup.zpowers_le.2 (by rw [MulAction.mem_stabilizer_iff, RingAut.smul_def]; exact t.2)
      have := hst hτ
      rwa [MulAction.mem_stabilizer_iff, RingAut.smul_def] at this
    · intro t t' htt'
      exact Subtype.ext (Subtype.mk.inj htt')
  have hfh : f / orderOf σ + f / orderOf σ ≤ f := by
    have := Nat.div_le_div_left hh (by norm_num : 0 < 2) (a := f)
    omega
  calc Nat.card {t : K // σ t = t} * Nat.card {t : K // σ t = t}
      ≤ Nat.card S * Nat.card S := Nat.mul_le_mul hle hle
    _ = 2 ^ (f / orderOf σ + f / orderOf σ) := by rw [hcard, pow_add]
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hfh
    _ = Nat.card K := hK.symm

omit [Finite K] in
theorem sq_mul_map_det {σ : K ≃+* K} {m₀₀ m₀₁ m₁₀ m₁₁ α : K} {v w : K × K}
    (hv : m₀₀ * v.1 + m₀₁ * v.2 = α * σ v.1 ∧ m₁₀ * v.1 + m₁₁ * v.2 = α * σ v.2)
    (hw : m₀₀ * w.1 + m₀₁ * w.2 = α * σ w.1 ∧ m₁₀ * w.1 + m₁₁ * w.2 = α * σ w.2) :
    α ^ 2 * σ (v.1 * w.2 - w.1 * v.2) = (m₀₀ * m₁₁ - m₀₁ * m₁₀) * (v.1 * w.2 - w.1 * v.2) := by
  rw [map_sub, map_mul, map_mul]
  linear_combination (-(α * σ w.2)) * hv.1 - (m₀₀ * v.1 + m₀₁ * v.2) * hw.2 +
    (α * σ v.2) * hw.1 + (m₀₀ * w.1 + m₀₁ * w.2) * hv.2

theorem card_le_of_forall_mul_eq_smul_map {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {σ : K ≃+* K} (hσ : σ ≠ 1) {S : Set (K × K)} {m₀₀ m₀₁ m₁₀ m₁₁ α : K} (hα : α ≠ 0)
    (hS : ∀ v ∈ S, m₀₀ * v.1 + m₀₁ * v.2 = α * σ v.1 ∧ m₁₀ * v.1 + m₁₁ * v.2 = α * σ v.2) :
    Nat.card S ≤ Nat.card K := by
  by_contra hlt
  push Not at hlt
  obtain ⟨p, hp, q, hq, hd⟩ := exists_independent_of_card_lt hlt
  have hσd : σ (p.1 * q.2 - q.1 * p.2) ≠ 0 := (map_ne_zero σ).2 hd
  have hfix : ∀ v ∈ S, ∀ w ∈ S, σ ((v.1 * w.2 - w.1 * v.2) / (p.1 * q.2 - q.1 * p.2)) =
      (v.1 * w.2 - w.1 * v.2) / (p.1 * q.2 - q.1 * p.2) := by
    intro v hv w hw
    have h1 := sq_mul_map_det (hS v hv) (hS w hw)
    have h2 := sq_mul_map_det (hS p hp) (hS q hq)
    rw [map_div₀, div_eq_div_iff hσd hd]
    apply mul_left_cancel₀ (pow_ne_zero 2 hα)
    linear_combination (p.1 * q.2 - q.1 * p.2) * h1 - (v.1 * w.2 - w.1 * v.2) * h2
  let Φ : S → {t : K // σ t = t} × {t : K // σ t = t} := fun w =>
    (⟨_, hfix w w.2 q hq⟩, ⟨_, hfix p hp w w.2⟩)
  have hΦ : Function.Injective Φ := by
    rintro ⟨w, hw⟩ ⟨w', hw'⟩ h
    simp only [Φ, Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [div_left_inj' hd] at h1 h2
    have e1 : w.1 * (p.1 * q.2 - q.1 * p.2) = w'.1 * (p.1 * q.2 - q.1 * p.2) := by
      linear_combination p.1 * h1 + q.1 * h2
    have e2 : w.2 * (p.1 * q.2 - q.1 * p.2) = w'.2 * (p.1 * q.2 - q.1 * p.2) := by
      linear_combination p.2 * h1 + q.2 * h2
    exact Subtype.ext (Prod.ext (mul_right_cancel₀ hd e1) (mul_right_cancel₀ hd e2))
  have := Nat.card_le_card_of_injective Φ hΦ
  rw [Nat.card_prod] at this
  exact absurd (this.trans (card_fix_mul_card_fix_le hf hK hσ)) (not_le.2 hlt)

omit [Finite K] in
theorem entries_of_mul_eq_zero {M : Matrix (Fin 3) (Fin 3) K} {a c a' c' : K}
    (h : !![0, a, c; 0, 0, 0; 0, 0, 0] * M = M * !![0, a', c'; 0, 0, 0; 0, 0, 0]) :
    M 1 0 * a' = 0 ∧ M 1 0 * c' = 0 ∧ M 2 0 * a' = 0 ∧ M 2 0 * c' = 0 ∧
      M 1 1 * a + M 2 1 * c = M 0 0 * a' ∧ M 1 2 * a + M 2 2 * c = M 0 0 * c' := by
  have e := fun i j => congrFun (congrFun h i) j
  have e11 := e 1 1
  have e12 := e 1 2
  have e21 := e 2 1
  have e22 := e 2 2
  have e01 := e 0 1
  have e02 := e 0 2
  simp [Matrix.mul_apply, Fin.sum_univ_three] at e11 e12 e21 e22 e01 e02
  exact ⟨mul_eq_zero.2 e11, mul_eq_zero.2 e12, mul_eq_zero.2 e21, mul_eq_zero.2 e22,
    by linear_combination e01, by linear_combination e02⟩

omit [Finite K] in
theorem entries_of_mul_eq_one {M : Matrix (Fin 3) (Fin 3) K} {a c a' c' : K}
    (h : !![0, a, c; 0, 0, 0; 0, 0, 0] * M = M * !![0, 0, 0; a', 0, 0; c', 0, 0]) :
    M 1 1 * a + M 2 1 * c = 0 ∧ M 1 2 * a + M 2 2 * c = 0 := by
  have e01 := congrFun (congrFun h 0) 1
  have e02 := congrFun (congrFun h 0) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three] at e01 e02
  exact ⟨by linear_combination e01, by linear_combination e02⟩

omit [Finite K] in
theorem mul_eq_of_conjAut_mul_fieldAut_fix (A : GL (Fin 3) K) (σ : K ≃+* K) (a c : K)
    (h : (conjAut 3 K A * fieldAut 3 K σ) (proj 3 K (unipU K a 0 c)) =
      proj 3 K (unipU K a 0 c)) :
    !![0, a, c; 0, 0, 0; 0, 0, 0] * (A : Matrix (Fin 3) (Fin 3) K) =
      (A : Matrix (Fin 3) (Fin 3) K) * !![0, σ a, σ c; 0, 0, 0; 0, 0, 0] := by
  rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj] at h
  refine CFSG.SeitzReduction.LinearPilot.mul_eq_of_proj_eq A ?_ ?_ ?_ ?_ (k := 0) ?_ h
  · rw [coe_slConjugation, SpecialLinearGroup.map_apply_coe, coe_unipU]
    congr 2
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · rw [coe_unipU]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  · simp

omit [Finite K] in
theorem mul_eq_of_conjAut_mul_fieldAut_mul_dualAut_fix (A : GL (Fin 3) K) (σ : K ≃+* K)
    (a c : K)
    (h : (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K) (proj 3 K (unipU K a 0 c)) =
      proj 3 K (unipU K a 0 c)) :
    !![0, a, c; 0, 0, 0; 0, 0, 0] * (A : Matrix (Fin 3) (Fin 3) K) =
      (A : Matrix (Fin 3) (Fin 3) K) * !![0, 0, 0; -σ a, 0, 0; -σ c, 0, 0] := by
  rw [MulAut.mul_apply, MulAut.mul_apply, dualAut_proj, fieldAut_proj, conjAut_proj] at h
  refine CFSG.SeitzReduction.LinearPilot.mul_eq_of_proj_eq A ?_ ?_ ?_ ?_ (k := 0) ?_ h
  · rw [coe_slConjugation, SpecialLinearGroup.map_apply_coe, SpecialLinearGroup.coe_transpose,
      unipU_inv, coe_unipU]
    congr 2
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · rw [coe_unipU]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  · simp

omit [Finite K] in
theorem conjAut_mem_range_conj_of_eq_smul (A : GL (Fin 3) K) (g : SpecialLinearGroup (Fin 3) K)
    {α : K} (hα : α ≠ 0)
    (h : (A : Matrix (Fin 3) (Fin 3) K) = α • (g : Matrix (Fin 3) (Fin 3) K)) :
    conjAut 3 K A ∈ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := by
  have hA : A = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 α hα) *
      SpecialLinearGroup.toGL g := by
    apply Units.ext
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, SpecialLinearGroup.coe_GL_coe_matrix,
      Units.val_mk0, h, scalar_apply, ← smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
  exact ⟨proj 3 K g, by rw [hA, map_mul, conjAut_scalar, one_mul, conjAut_toGL]⟩

theorem card_le_of_fix_projRad_zero {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {F : Subgroup (projectiveSL 3 K)} (hFR : F ≤ projRad K 0) {x : MulAut (projectiveSL 3 K)}
    (hx : ∀ a ∈ F, x a = a)
    (hxi : x ∉ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range) :
    Nat.card F ≤ Nat.card K := by
  set S : Set (K × K) := {v | proj 3 K (unipU K v.1 0 v.2) ∈ F}
  have hFS : Nat.card F ≤ Nat.card S := by
    refine Nat.card_le_card_of_surjective
      (fun v : S => (⟨proj 3 K (unipU K v.1.1 0 v.1.2), v.2⟩ : F)) ?_
    rintro ⟨y, hy⟩
    obtain ⟨a, c, rfl⟩ := mem_projRad_zero.1 (hFR hy)
    exact ⟨⟨(a, c), hy⟩, rfl⟩
  by_contra hlt
  push Not at hlt
  have hlt' : Nat.card K < Nat.card S := hlt.trans_le hFS
  obtain ⟨p, hp, q, hq, hd⟩ := exists_independent_of_card_lt hlt'
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (K := K) (n := 3) le_rfl).2 x
  have hfix : ∀ v ∈ S, (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K ^ ε)
      (proj 3 K (unipU K v.1 0 v.2)) = proj 3 K (unipU K v.1 0 v.2) := fun v hv => hx _ hv
  have hdet : (A : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero A
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · simp only [pow_zero, mul_one] at hfix hxi
    have key := fun v (hv : v ∈ S) =>
      entries_of_mul_eq_zero (mul_eq_of_conjAut_mul_fieldAut_fix A σ v.1 v.2 (hfix v hv))
    have hp0 : σ p.1 ≠ 0 ∨ σ p.2 ≠ 0 := by
      by_contra h0
      push Not at h0
      simp only [map_eq_zero] at h0
      apply hd
      rw [h0.1, h0.2]
      ring
    obtain ⟨k10, k10', k20, k20', -, -⟩ := key p hp
    have h10 : (A : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := by
      rcases hp0 with h | h
      · exact (mul_eq_zero.1 k10).resolve_right h
      · exact (mul_eq_zero.1 k10').resolve_right h
    have h20 : (A : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
      rcases hp0 with h | h
      · exact (mul_eq_zero.1 k20).resolve_right h
      · exact (mul_eq_zero.1 k20').resolve_right h
    have hα : (A : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := by
      intro h0
      apply hdet
      rw [det_fin_three, h0, h10, h20]
      ring
    by_cases hσ : σ = 1
    ·
      subst hσ
      apply hxi
      rw [map_one, mul_one]
      obtain ⟨-, -, -, -, kp1, kp2⟩ := key p hp
      obtain ⟨-, -, -, -, kq1, kq2⟩ := key q hq
      simp only [RingAut.one_apply] at kp1 kp2 kq1 kq2
      obtain ⟨h11, h21⟩ := eq_zero_of_independent hd
        (x := (A : Matrix (Fin 3) (Fin 3) K) 1 1 - (A : Matrix (Fin 3) (Fin 3) K) 0 0)
        (y := (A : Matrix (Fin 3) (Fin 3) K) 2 1)
        (by linear_combination kp1) (by linear_combination kq1)
      obtain ⟨h12, h22⟩ := eq_zero_of_independent hd
        (x := (A : Matrix (Fin 3) (Fin 3) K) 1 2)
        (y := (A : Matrix (Fin 3) (Fin 3) K) 2 2 - (A : Matrix (Fin 3) (Fin 3) K) 0 0)
        (by linear_combination kp2) (by linear_combination kq2)
      refine conjAut_mem_range_conj_of_eq_smul A
        (unipU K ((A : Matrix (Fin 3) (Fin 3) K) 0 1 / (A : Matrix (Fin 3) (Fin 3) K) 0 0) 0
          ((A : Matrix (Fin 3) (Fin 3) K) 0 2 / (A : Matrix (Fin 3) (Fin 3) K) 0 0)) hα ?_
      rw [sub_eq_zero] at h11 h22
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [coe_unipU, h10, h20, h11, h21, h12, h22, mul_div_cancel₀ _ hα]
    ·
      exact absurd (card_le_of_forall_mul_eq_smul_map hf hK hσ hα fun v hv =>
        ⟨(key v hv).2.2.2.2.1, (key v hv).2.2.2.2.2⟩) (not_le.2 hlt')
  ·
    simp only [pow_one] at hfix
    have key := fun v (hv : v ∈ S) => entries_of_mul_eq_one
      (mul_eq_of_conjAut_mul_fieldAut_mul_dualAut_fix A σ v.1 v.2 (hfix v hv))
    obtain ⟨kp1, kp2⟩ := key p hp
    obtain ⟨kq1, kq2⟩ := key q hq
    obtain ⟨h11, h21⟩ := eq_zero_of_independent hd kp1 kq1
    obtain ⟨h12, h22⟩ := eq_zero_of_independent hd kp2 kq2
    apply hdet
    rw [det_fin_three, h11, h21, h12, h22]
    ring

theorem fix_map_of_fix {G : Type*} [Group G] {F : Subgroup G} {x : MulAut G}
    (hx : ∀ a ∈ F, x a = a) (τ : MulAut G) :
    ∀ a ∈ F.map (τ : G →* G), (τ * x * τ⁻¹) a = a := by
  rintro _ ⟨a, ha, rfl⟩
  simp only [MulAut.mul_apply, MonoidHom.coe_ofClass, MulAut.inv_apply, MulEquiv.symm_apply_apply,
    hx a ha]

theorem conj_mul_not_mem_range {G : Type*} [Group G] {x : MulAut G}
    (hxi : x ∉ (MulAut.conj : G →* MulAut G).range) (τ : MulAut G) :
    τ * x * τ⁻¹ ∉ (MulAut.conj : G →* MulAut G).range := by
  rintro ⟨g, hg⟩
  refine hxi ⟨τ⁻¹ g, ?_⟩
  rw [CFSG.ComponentClassification.RankTwoL3Even.conj_map_eq, hg]
  group

omit [Finite K] in
theorem exists_mulAut_map_projRad_one :
    ∃ τ : MulAut (projectiveSL 3 K), ∀ y ∈ projRad K 1, τ y ∈ projRad K 0 := by
  have hW : (!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) K) *
      !![0, 0, 1; 0, 1, 0; 1, 0, 0] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  refine ⟨conjAut 3 K ⟨_, _, hW, hW⟩ * dualAut 3 K, fun y hy => ?_⟩
  obtain ⟨b, c, rfl⟩ := mem_projRad_one.1 hy
  rw [MulAut.mul_apply, dualAut_proj, conjAut_proj]
  refine mem_projRad_zero.2 ⟨-b, -c, congrArg _ (Subtype.ext ?_)⟩
  rw [coe_slConjugation, SpecialLinearGroup.coe_transpose, unipU_inv, coe_unipU, coe_unipU]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem card_le_of_fix_projRad_one {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {F : Subgroup (projectiveSL 3 K)} (hFR : F ≤ projRad K 1) {x : MulAut (projectiveSL 3 K)}
    (hx : ∀ a ∈ F, x a = a)
    (hxi : x ∉ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range) :
    Nat.card F ≤ Nat.card K := by
  obtain ⟨τ, hτ⟩ := exists_mulAut_map_projRad_one (K := K)
  have h := card_le_of_fix_projRad_zero hf hK (F := F.map (τ : projectiveSL 3 K →* _))
    (by rintro _ ⟨y, hy, rfl⟩; exact hτ y (hFR hy)) (fix_map_of_fix hx τ)
    (conj_mul_not_mem_range hxi τ)
  rwa [Subgroup.card_map_of_injective τ.injective] at h

omit [Finite K] in
theorem le_projRad_of_le_projUnip [CharP K 2] {F : Subgroup (projectiveSL 3 K)}
    (hFU : F ≤ projUnip K) (hF2 : ∀ a ∈ F, a ^ 2 = 1) : F ≤ projRad K 0 ∨ F ≤ projRad K 1 := by
  have hsq : ∀ g ∈ F.comap (proj 3 K) ⊓ unipAll K, g * g = 1 := by
    rintro g ⟨hgF, hgU⟩
    obtain ⟨a, b, c, hg⟩ := CFSG.OddStandard.Seitz77.mem_unipAll.1 (mul_mem hgU hgU)
    have h1 : proj 3 K (unipU K a b c) = 1 := by
      rw [hg, map_mul, ← sq]
      exact hF2 _ hgF
    obtain ⟨rfl, rfl, rfl⟩ := proj_unipU_eq_one_iff.1 h1
    rw [← hg, unipU_zero]
  have hlift : ∀ y ∈ F, ∃ g ∈ F.comap (proj 3 K) ⊓ unipAll K, proj 3 K g = y := by
    intro y hy
    obtain ⟨g, hg, rfl⟩ := hFU hy
    exact ⟨g, ⟨hy, hg⟩, rfl⟩
  rcases CFSG.OddStandard.Seitz77.le_unipOne_or_le_unipTwo _ inf_le_right hsq with h | h
  · refine Or.inl fun y hy => ?_
    obtain ⟨g, hg, rfl⟩ := hlift y hy
    rw [projRad_zero]
    exact ⟨g, h hg, rfl⟩
  · refine Or.inr fun y hy => ?_
    obtain ⟨g, hg, rfl⟩ := hlift y hy
    rw [projRad_one]
    exact ⟨g, h hg, rfl⟩

theorem exists_conj_le_projUnip [CharP K 2] {F : Subgroup (projectiveSL 3 K)}
    (hF2 : ∀ a ∈ F, a ^ 2 = 1) : ∃ g : projectiveSL 3 K, ∀ a ∈ F, g⁻¹ * a * g ∈ projUnip K := by
  have hp : IsPGroup 2 F := fun a => ⟨1, Subtype.ext (by rw [pow_one]; exact hF2 a a.2)⟩
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := CFSG.SeitzReduction.LinearPilot.exists_conj_projUnitriangular (by norm_num) Q
  refine ⟨g, fun a ha => ?_⟩
  rw [projUnip_eq_projUnitriangular, ← hg]
  exact hQ ha

theorem card_le_of_forall_fix_of_sq {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {F : Subgroup (projectiveSL 3 K)} (hF2 : ∀ a ∈ F, a ^ 2 = 1)
    {x : MulAut (projectiveSL 3 K)} (hx : ∀ a ∈ F, x a = a)
    (hxi : x ∉ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range) :
    Nat.card F ≤ Nat.card K := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  obtain ⟨g, hg⟩ := exists_conj_le_projUnip hF2
  set τ := MulAut.conj g⁻¹ with hτ
  set F' := F.map (τ : projectiveSL 3 K →* projectiveSL 3 K)
  have hF'U : F' ≤ projUnip K := by
    rintro _ ⟨a, ha, rfl⟩
    simpa [hτ, MulAut.conj_apply] using hg a ha
  have hF'2 : ∀ a ∈ F', a ^ 2 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [MonoidHom.coe_ofClass, ← map_pow, hF2 a ha, map_one]
  rw [← Subgroup.card_map_of_injective (f := (τ : projectiveSL 3 K →* projectiveSL 3 K))
    τ.injective]
  rcases le_projRad_of_le_projUnip hF'U hF'2 with h | h
  · exact card_le_of_fix_projRad_zero hf hK h (fix_map_of_fix hx τ) (conj_mul_not_mem_range hxi τ)
  · exact card_le_of_fix_projRad_one hf hK h (fix_map_of_fix hx τ) (conj_mul_not_mem_range hxi τ)

theorem card_le_of_forall_fix {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {F : Subgroup (projectiveSL 3 K)} (hF : CFSG.Open.IsElemAbelian 2 F)
    {x : MulAut (projectiveSL 3 K)} (hx : ∀ a ∈ F, x a = a)
    (hxi : x ∉ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range) :
    Nat.card F ≤ Nat.card K :=
  card_le_of_forall_fix_of_sq hf hK hF.2 hx hxi

theorem relIndex_semilinearAutGroup_le (E : Subgroup (MulAut (projectiveSL 3 K))) :
    (semilinearAutGroup 3 K).relIndex E ≤ 2 := by
  have h := (standard_outer_quotients (K := K) (n := 3)).2.2.2.2.2.2.2.1
  rw [(automorphism_generation (K := K) (n := 3) le_rfl).1] at h
  have h' : (semilinearAutGroup 3 K).relIndex ⊤ ≤ 2 := h
  refine (Subgroup.relIndex_le_of_le_right le_top ?_).trans h'
  rw [Subgroup.relIndex_top_right]
  exact Subgroup.index_ne_zero_of_finite

theorem relIndex_ker_eq {G Q : Type*} [Group G] [Group Q] (φ : G →* Q) (H : Subgroup G) :
    φ.ker.relIndex H = Nat.card (H.map φ) := by
  rw [Subgroup.relIndex, ← MonoidHom.ker_domRestrict, Subgroup.index_ker,
    MonoidHom.domRestrict_range]

theorem card_le_two_of_isCyclic {Q : Type*} [Group Q] [IsCyclic Q] (H : Subgroup Q)
    (hH : ∀ y ∈ H, y ^ 2 = 1) : Nat.card H ≤ 2 := by
  have h1 : Monoid.exponent H ∣ 2 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun y => Subtype.ext (by simpa using hH y y.2)
  rw [IsCyclic.exponent_eq_card] at h1
  exact Nat.le_of_dvd (by norm_num) h1

theorem card_le_four_mul_card_inf_range {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {E : Subgroup (MulAut (projectiveSL 3 K))} (hE : CFSG.Open.IsElemAbelian 2 E) :
    Nat.card E ≤
      4 * Nat.card ↥(E ⊓ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range) := by
  set S := semilinearAutGroup 3 K
  set φ := ProjectivePlane.linearFieldPart K (n := 3) le_rfl
  set I := (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range
  obtain ⟨σ₀, -, -, hσ₀, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two hf hK
  have : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨σ₀, hσ₀⟩
  have h1 : Nat.card E ≤ 2 * Nat.card ↥(S ⊓ E) := by
    rw [← Subgroup.relIndex_mul_card S E]
    exact Nat.mul_le_mul_right _ (relIndex_semilinearAutGroup_le E)
  have h2 : Nat.card ↥(S ⊓ E) ≤ 2 * Nat.card ↥(φ.ker ⊓ (S ⊓ E)) := by
    rw [← Subgroup.relIndex_mul_card φ.ker (S ⊓ E), relIndex_ker_eq]
    refine Nat.mul_le_mul_right _ (card_le_two_of_isCyclic _ ?_)
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, hE.2 y hy.2, map_one]
  have h3 : φ.ker ⊓ (S ⊓ E) ≤ E ⊓ I := by
    rintro y ⟨hyφ, hyS, hyE⟩
    refine ⟨hyE, ?_⟩
    obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.1 hyS
    have hσ : σ = 1 := by
      have := ProjectivePlane.linearFieldPart_eq (K := K) (n := 3) le_rfl (A := A) (σ := σ)
        zero_le_one
      rw [pow_zero, mul_one] at this
      rw [← this]
      exact hyφ
    subst hσ
    rw [map_one, mul_one] at hyE ⊢
    exact CFSG.ComponentClassification.RankTwoL3Even.mem_inner_of_mem_linearAutGroup
      (conjAut_mem_linearAutGroup A) (k := 1) (by rw [pow_one]; exact hE.2 _ hyE)
  calc Nat.card E ≤ 2 * Nat.card ↥(S ⊓ E) := h1
    _ ≤ 2 * (2 * Nat.card ↥(φ.ker ⊓ (S ⊓ E))) := Nat.mul_le_mul_left _ h2
    _ ≤ 2 * (2 * Nat.card ↥(E ⊓ I)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Subgroup.card_le_of_le h3))
    _ = 4 * Nat.card ↥(E ⊓ I) := by ring

theorem card_le_of_not_le_range {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {E : Subgroup (MulAut (projectiveSL 3 K))} (hE : CFSG.Open.IsElemAbelian 2 E)
    (hout : ¬ E ≤ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range) :
    Nat.card E ≤ 4 * Nat.card K := by
  obtain ⟨x, hxE, hxI⟩ := IsConcreteLE.not_le_iff_exists.1 hout
  set F := E.comap (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K))
  have hinj := CFSG.ComponentClassification.RankTwoL3Even.conj_injective_projectiveSL (F := K)
  have hF2 : ∀ a ∈ F, a ^ 2 = 1 := fun a ha => hinj (by rw [map_pow, hE.2 _ ha, map_one])
  have hfix : ∀ a ∈ F, x a = a := by
    intro a ha
    apply hinj
    have hc : x * MulAut.conj a = MulAut.conj a * x :=
      congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hxE⟩ ⟨MulAut.conj a, ha⟩)
    rw [CFSG.ComponentClassification.RankTwoL3Even.conj_map_eq, hc, mul_inv_cancel_right]
  have hcard : Nat.card ↥(E ⊓ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range)
      = Nat.card F := by
    rw [inf_comm, ← Subgroup.map_comap_eq, Subgroup.card_map_of_injective hinj]
  calc Nat.card E ≤ 4 * Nat.card ↥(E ⊓
        (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range) :=
      card_le_four_mul_card_inf_range hf hK hE
    _ = 4 * Nat.card F := by rw [hcard]
    _ ≤ 4 * Nat.card K := Nat.mul_le_mul_left _ (card_le_of_forall_fix_of_sq hf hK hF2 hfix hxI)

end F7

theorem exists_conj_canonical_of_not_mem_range {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {y : MulAut (projectiveSL 3 K)} (hy : y ^ 2 = 1)
    (hout : y ∉ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range) :
    (Even f ∧ ∃ σ : K ≃+* K, (∀ x, σ x = x ^ 2 ^ (f / 2)) ∧
        ∃ γ : MulAut (projectiveSL 3 K), y = γ * fieldAut 3 K σ * γ⁻¹) ∨
      (∃ γ : MulAut (projectiveSL 3 K), y = γ * dualAut 3 K * γ⁻¹) ∨
      (Even f ∧ ∃ σ : K ≃+* K, (∀ x, σ x = x ^ 2 ^ (f / 2)) ∧
        ∃ γ : MulAut (projectiveSL 3 K), y = γ * (fieldAut 3 K σ * dualAut 3 K) * γ⁻¹) := by
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (K := K) (n := 3) le_rfl).2 y
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  · rw [pow_zero, mul_one] at hout hy ⊢
    by_cases hσ : σ = 1
    · exfalso
      subst hσ
      rw [map_one, mul_one] at hout hy
      exact hout (ComponentClassification.RankTwoL3Even.mem_inner_of_mem_linearAutGroup
        (conjAut_mem_linearAutGroup A) (k := 1) hy)
    · obtain ⟨hfe, hσx, H, hH⟩ :=
        even_linear_field_involution_descent (n := 3) hf hK le_rfl A σ hσ hy
      exact Or.inl ⟨hfe, σ, hσx, conjAut 3 K H, hH⟩
  · rw [pow_one] at hout hy ⊢
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one, mul_one] at hy ⊢
      obtain ⟨-, ⟨H, C, -, hH, hC⟩, -⟩ :=
        UnitaryHigher.even_linear_pure_graph_involution_normal_forms (n := 3) hf hK le_rfl A hy
      have hC1 : C = 1 := by
        rcases hC with ⟨hC1, -⟩ | ⟨r, hr, -⟩
        · exact Units.ext hC1
        · omega
      subst hC1
      rw [map_one, one_mul] at hH
      exact Or.inr (Or.inl ⟨conjAut 3 K H, hH⟩)
    · obtain ⟨hfe, hσx, H, hH⟩ :=
        UnitaryHigher.linear_graph_field_involution_descent Nat.prime_two hf hK le_rfl A σ hσ hy
      exact Or.inr (Or.inr ⟨hfe, σ, hσx, conjAut 3 K H, hH⟩)

theorem exists_conj_eq_mul_conj_of_not_mem_range {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {y : MulAut (projectiveSL 3 K)} (hy : y ^ 2 = 1)
    (hout : y ∉ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range)
    {p : projectiveSL 3 K} (hp : (y * MulAut.conj p) ^ 2 = 1) :
    ∃ b : projectiveSL 3 K, MulAut.conj b * y * (MulAut.conj b)⁻¹ = y * MulAut.conj p := by
  have hinj := ComponentClassification.RankTwoL3Even.conj_injective_projectiveSL (F := K)
  have hy' : y * y = 1 := by rw [← sq, hy]
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy'
  have hconj : ∀ w : projectiveSL 3 K, MulAut.conj (y w) = y * MulAut.conj w * y⁻¹ := fun w =>
    (SeitzReduction.LinearPilot.mulAut_mul_conj_mul_inv_eq_conj y w).symm
  have hyp : y p = p⁻¹ := by
    apply hinj
    rw [hconj, map_inv, eq_inv_iff_mul_eq_one, hyinv, ← hp, sq]
    group
  obtain ⟨w, hw⟩ := isLangSurjective_of_not_mem_range hf hK hy hout p hyp
  refine ⟨w⁻¹, ?_⟩
  have h1 : y p = w⁻¹ * y w := by
    rw [← hw, map_mul, map_inv, ← MulAut.mul_apply, hy', MulAut.one_apply]
  have h2 : y * MulAut.conj p = MulAut.conj (y p) * y := by
    rw [hconj, inv_mul_cancel_right]
  rw [h2, h1, map_mul, hconj, map_inv, inv_inv]
  group

end CFSG.LocalAnalysis.EvenBN.LinearThree
