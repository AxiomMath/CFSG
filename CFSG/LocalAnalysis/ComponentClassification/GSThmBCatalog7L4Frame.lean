module

public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecPGL
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4TFrameL
public import CFSG.LocalAnalysis.SteinbergCDEvenLinearThreeSemilinearFixed

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7L4

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.CatalogueBProjectiveInvolution
open CFSG.ComponentClassification.CatFactsL4U4.HBlocks

theorem exists_square_of_two_pComponents {F : Type} [Field F] [Finite F] (htwo : (2 : F) ≠ 0)
    {n : ℕ} (hn : 2 ≤ n) (A : GL (Fin n) F) (hne : ProjGenLinGroup.mk A ≠ 1)
    (hinv : ProjGenLinGroup.mk A ^ 2 = 1)
    {L₁ L₂ : Subgroup (centralizer ({ProjGenLinGroup.mk A} : Set _))}
    (h₁ : IsPComponent 2 L₁) (h₂ : IsPComponent 2 L₂) (hL : L₁ ≠ L₂) :
    ∃ b : Fˣ, A ^ 2 = GeneralLinearGroup.scalar (Fin n) (b ^ 2) ∧
      2 ≤ positiveMatrixDimension A b.val ∧ 2 ≤ negativeMatrixDimension A b.val := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have := ordinaryCentralizerProjection_range_normal A
  have := projectiveCentralizerModuloOrdinary_solvable A
  have hc : (ordinaryCentralizerProjection A).ker ≤ center (centralizer ({A} : Set _)) := by
    have := ordinaryCentralizerProjection_rangeRestrict_kernel_central A
    rwa [MonoidHom.ker_rangeRestrict] at this
  obtain ⟨M₁, M₂, hM₁, hM₂, hM⟩ :=
    Sp4Rec.exists_pComponent_lifts (ordinaryCentralizerProjection A) hc h₁ h₂ hL
  obtain ⟨lambda, hsq⟩ := matrix_square_scalar A hinv
  by_cases hsquare : IsSquare lambda.val
  · obtain ⟨b, hb, hr, hs, -, e, -⟩ :=
      square_projective_centralizer_structure n hn A lambda htwo hne hsq hsquare
    obtain ⟨h1, h2⟩ := Sp4Rec.two_le_of_two_pComponents_prod hr hs
      (CatalogueBAlternating.pComponent_map_equiv 2 e _ hM₁)
      (CatalogueBAlternating.pComponent_map_equiv 2 e _ hM₂)
      (fun h => hM (map_injective e.injective h))
    exact ⟨b, by rw [hsq, hb], h1, h2⟩
  · exfalso
    have : Fact (¬ IsSquare lambda.val) := ⟨hsquare⟩
    have : Finite (CatalogueBProjectiveQuadratic.extension lambda.val) :=
      quadraticExtension_finite lambda.val
    have hm := (CatalogueBProjectiveQuadratic.nonsquare_matrix_dimension n hn A lambda hsq
      hsquare).2
    let e := CatalogueBProjectiveQuadratic.matrixCentralizerQuadraticEquiv A lambda hsq
    obtain ⟨-, -, -, k₁, -⟩ := CatalogueBGeneralLinear.pComponent_classification _ _ hm 2 _
      (CatalogueBAlternating.pComponent_map_equiv 2 e _ hM₁)
    obtain ⟨-, -, -, k₂, -⟩ := CatalogueBGeneralLinear.pComponent_classification _ _ hm 2 _
      (CatalogueBAlternating.pComponent_map_equiv 2 e _ hM₂)
    exact hM (map_injective e.injective (k₁.trans k₂.symm))

theorem projToPGL_range_normal (n : ℕ) (k : Type) [Field k] :
    (LocalAnalysis.SteinbergCD.projToPGL n k).range.Normal := by
  constructor
  rintro _ ⟨y, rfl⟩ B
  obtain ⟨g, rfl⟩ := proj_surjective n k y
  obtain ⟨B, rfl⟩ := ProjGenLinGroup.mk_surjective B
  have hdet : ((B * SpecialLinearGroup.toGL g * B⁻¹ : GL (Fin n) k) :
      Matrix (Fin n) (Fin n) k).det = 1 := by
    simp only [Units.val_mul, det_mul, SpecialLinearGroup.coe_GL_coe_matrix, g.2, mul_one]
    rw [← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]
  let g' : SpecialLinearGroup (Fin n) k := ⟨_, hdet⟩
  have hU : SpecialLinearGroup.toGL g' = B * SpecialLinearGroup.toGL g * B⁻¹ := Units.ext rfl
  refine ⟨proj n k g', ?_⟩
  rw [LocalAnalysis.SteinbergCD.projToPGL_proj, LocalAnalysis.SteinbergCD.projToPGL_proj, hU]
  simp only [map_mul, map_inv]

theorem exists_square_of_pairConfig {k : Type} [Field k] [Finite k] (htwo : (2 : k) ≠ 0)
    {n : ℕ} (hn : 2 ≤ n) {g : SpecialLinearGroup (Fin n) k} {K₁ K₂ : Subgroup (projectiveSL n k)}
    (hc : Sp4Rec.PairConfig (projectiveSL n k) (proj n k g) K₁ K₂) :
    ∃ b : kˣ, SpecialLinearGroup.toGL g ^ 2 = GeneralLinearGroup.scalar (Fin n) (b ^ 2) ∧
      2 ≤ positiveMatrixDimension (SpecialLinearGroup.toGL g) b.val ∧
      2 ≤ negativeMatrixDimension (SpecialLinearGroup.toGL g) b.val := by
  classical
  have : Finite (ProjGenLinGroup (Fin n) k) :=
    Finite.of_surjective _ ProjGenLinGroup.mk_surjective
  set φ := LocalAnalysis.SteinbergCD.projToPGL n k with hφdef
  have hφ : Function.Injective φ := LocalAnalysis.SteinbergCD.projToPGL_injective
  have := projToPGL_range_normal n k
  have hA : φ (proj n k g) = ProjGenLinGroup.mk (SpecialLinearGroup.toGL g) :=
    LocalAnalysis.SteinbergCD.projToPGL_proj g
  have hx2 : proj n k g ^ 2 = 1 := by rw [← hc.orderOf_x, pow_orderOf_eq_one]
  have hne : ProjGenLinGroup.mk (SpecialLinearGroup.toGL g) ≠ 1 := by
    rw [← hA]
    intro h
    have h1 : proj n k g = 1 := hφ (h.trans (map_one φ).symm)
    have := hc.orderOf_x
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  have hinv : ProjGenLinGroup.mk (SpecialLinearGroup.toGL g) ^ 2 = 1 := by
    rw [← hA, ← map_pow, hx2, map_one]
  obtain ⟨-, hK⟩ := Sp4Rec.isPComponent_map_of_normal φ hφ hc.K_le hc.isPComponent_K
  obtain ⟨hK'le, hK'⟩ := Sp4Rec.isPComponent_map_of_normal φ hφ hc.K'_le hc.isPComponent_K'
  have hKle : K₁.map φ ≤ centralizer ({φ (proj n k g)} : Set _) :=
    (Sp4Rec.isPComponent_map_of_normal φ hφ hc.K_le hc.isPComponent_K).1
  rw [hA] at hK hK' hKle hK'le
  refine exists_square_of_two_pComponents htwo hn _ hne hinv hK hK' fun h => hc.ne ?_
  have h1 := subgroupOf_inj.mp h
  rw [inf_of_le_left hKle, inf_of_le_left hK'le] at h1
  exact map_injective hφ h1

theorem X1_eq_smul {k : Type} [Field k] (b : k) : X1 b = b • X1 (1 : k) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [X1]

theorem exists_frame_of_pairConfig {k : Type} [Field k] [Finite k] (htwo : (2 : k) ≠ 0)
    {g : SpecialLinearGroup (Fin 4) k} {K₁ K₂ : Subgroup (projectiveSL 4 k)}
    (hc : Sp4Rec.PairConfig (projectiveSL 4 k) (proj 4 k g) K₁ K₂) :
    ∃ (b : kˣ) (P : GL (Fin 4) k), b ^ 4 = 1 ∧
      (g : Matrix (Fin 4) (Fin 4) k) * (P : Matrix (Fin 4) (Fin 4) k) =
        (P : Matrix (Fin 4) (Fin 4) k) * X1 (b : k) := by
  classical
  obtain ⟨b, hsq, hp, hm⟩ := exists_square_of_pairConfig htwo (by norm_num) hc
  set A := SpecialLinearGroup.toGL g with hAdef
  set T := splitMatrixOperator A with hTdef
  have hT2 := splitMatrixOperator_square A b hsq
  have hcompl := squareScalar_eigenspaces_isCompl T b.val b.ne_zero htwo hT2
  have hsum := splitMatrixDimension_sum A b htwo hsq
  rw [Fintype.card_fin] at hsum
  have hp2 : positiveMatrixDimension A b.val = 2 := by omega
  have hm2 : negativeMatrixDimension A b.val = 2 := by omega
  have hdetT := CatFactsL4U4.det_eq_of_isCompl_smul hcompl
    (fun v hv => (Module.End.mem_eigenspace_iff).1 hv)
    (fun v hv => (Module.End.mem_eigenspace_iff).1 hv)
  have hdT : LinearMap.det T = 1 := by
    rw [hTdef, splitMatrixOperator, CatalogueBProjectiveCoordinates.matrixActionEquiv_toLinearMap]
    change LinearMap.det (Matrix.toLin' (g : Matrix (Fin 4) (Fin 4) k)) = 1
    rw [LinearMap.det_toLin']
    exact g.2
  change LinearMap.det T = b.val ^ positiveMatrixDimension A b.val *
    (-b.val) ^ negativeMatrixDimension A b.val at hdetT
  rw [hp2, hm2, hdT] at hdetT
  have hb4 : b ^ 4 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, hdetT]
    ring
  have hgg : (g : Matrix (Fin 4) (Fin 4) k) * (g : Matrix (Fin 4) (Fin 4) k) =
      (b.val ^ 2) • (1 : Matrix (Fin 4) (Fin 4) k) := by
    have h := congrArg (fun M : GL (Fin 4) k => (M : Matrix (Fin 4) (Fin 4) k)) hsq
    simp only [Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar, hAdef,
      SpecialLinearGroup.coe_GL_coe_matrix] at h
    rw [← pow_two, h]
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  set X : Matrix (Fin 4) (Fin 4) k := (b.val)⁻¹ • (g : Matrix (Fin 4) (Fin 4) k) with hX
  have hbv : (b.val : k) ≠ 0 := b.ne_zero
  have hXX : X * X = 1 := by
    rw [hX, smul_mul_smul_comm, hgg, smul_smul, ← pow_two, inv_pow, inv_mul_cancel₀
      (pow_ne_zero 2 hbv), one_smul]
  have hdX : X.det = 1 := by
    rw [hX, det_smul, g.2, mul_one, Fintype.card_fin, inv_pow]
    have : (b.val) ^ 4 = 1 := by rw [← Units.val_pow_eq_pow_val, hb4, Units.val_one]
    rw [this, inv_one]
  have hx1 : proj 4 k g ≠ 1 := by
    intro h
    have := hc.orderOf_x
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have hscal : ∀ c : k, X ≠ c • (1 : Matrix (Fin 4) (Fin 4) k) := by
    intro c hc'
    apply hx1
    rw [proj_eq_one_iff, mem_scalars]
    have hg : (g : Matrix (Fin 4) (Fin 4) k) = (b.val * c) • (1 : Matrix (Fin 4) (Fin 4) k) := by
      rw [mul_smul, ← hc', hX, smul_smul, mul_inv_cancel₀ hbv, one_smul]
    have hc0 : b.val * c ≠ 0 := by
      intro h0
      have := g.2
      rw [hg, h0, zero_smul, det_zero] at this
      exact zero_ne_one this
    refine ⟨Units.mk0 _ hc0, ?_, ?_⟩
    · apply Units.ext
      have := g.2
      rw [hg, det_smul, det_one, mul_one, Fintype.card_fin] at this
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, this, Units.val_one]
    · rw [hg]
      ext i j
      simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  have h1 : X ≠ 1 := fun h => hscal 1 (by rw [h, one_smul])
  have hm1 : X ≠ -1 := fun h => hscal (-1) (by rw [h, neg_one_smul])
  obtain ⟨P, hP⟩ := CatFactsL4U4.TBlocks.exists_frame_t2_L4 htwo hXX hdX h1 hm1
  refine ⟨b, P, hb4, ?_⟩
  have hgX : (g : Matrix (Fin 4) (Fin 4) k) = b.val • X := by
    rw [hX, smul_smul, mul_inv_cancel₀ hbv, one_smul]
  rw [hgX, smul_mul_assoc, hP, X1_eq_smul (b.val), mul_smul_comm]

end Catalog7L4

end CFSG.ComponentClassification.GSThmB
