module

public import CFSG.RankThree.PartOne.K159.Klein
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotTori
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Matrix QuadraticMap
open CFSG.LieType.Universal.Spin (quadPlus quadPlus_apply polar_quadPlus)
open CFSG.RankThree.PartOne.K159.Klein (alt coords cong cong_apply)
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

section KleinFacts

variable {K L : Type*} [Field K] [Field L]

omit [Field L] in
theorem alt_map [Field L] (φ : K →+* L) (v : Fin 3 ⊕ Fin 3 → K) :
    alt (fun s => φ (v s)) = (alt v).map φ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [alt, CFSG.LocalAnalysis.antiMat]

theorem coords_map (φ : K →+* L) (N : Matrix (Fin 4) (Fin 4) K) :
    coords (N.map φ) = fun s => φ (coords N s) := by
  funext s
  rcases s with i | i <;> fin_cases i <;> simp [coords]

theorem cong_map (φ : K →+* L) (M : Matrix (Fin 4) (Fin 4) K) (v : Fin 3 ⊕ Fin 3 → K) :
    cong (M.map φ) (fun s => φ (v s)) = fun s => φ (cong M v s) := by
  rw [cong_apply, cong_apply, alt_map, ← Matrix.transpose_map, ← Matrix.map_mul,
    ← Matrix.map_mul, coords_map]

theorem sum_cong_transpose_mul (M : Matrix (Fin 4) (Fin 4) K) (v w : Fin 3 ⊕ Fin 3 → K) :
    ∑ s, cong Mᵀ v s * w s = ∑ s, v s * cong M w s := by
  simp only [cong_apply, coords, alt, CFSG.LocalAnalysis.antiMat, Fintype.sum_sum_type,
    Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply,
    Sum.elim_inl, Sum.elim_inr]
  simp
  ring

theorem polar_quadPlus_three (v w : Fin 3 ⊕ Fin 3 → K) :
    polar (quadPlus 3 K) v w = ∑ s, v s.swap * w s := by
  rw [polar_quadPlus]
  simp only [Fintype.sum_sum_type, Fin.sum_univ_three, Sum.swap_inl, Sum.swap_inr]
  ring

theorem eq_of_forall_sum_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {x y : ι → K}
    (h : ∀ w : ι → K, ∑ s, x s * w s = ∑ s, y s * w s) : x = y := by
  funext t
  have := h (Pi.single t 1)
  simpa [Pi.single_apply] using this

variable [CharP K 2]

theorem cong_inverseTranspose_star (g : SpecialLinearGroup (Fin 4) K)
    (v : Fin 3 ⊕ Fin 3 → K) :
    cong (((g⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ)
        (fun s => v s.swap) = fun s => cong (g : Matrix (Fin 4) (Fin 4) K) v s.swap := by
  apply eq_of_forall_sum_mul
  intro w
  have hpol : ∀ x y : Fin 3 ⊕ Fin 3 → K,
      polar (quadPlus 3 K) (cong (g : Matrix (Fin 4) (Fin 4) K) x)
        (cong (g : Matrix (Fin 4) (Fin 4) K) y) = polar (quadPlus 3 K) x y := by
    intro x y
    have hm := CFSG.RankThree.PartOne.K159.Klein.rho_mem g
    simp only [polar, ← CFSG.RankThree.PartOne.K159.Klein.rho_apply, ← map_add,
      TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hm]
  have hinv : cong (g : Matrix (Fin 4) (Fin 4) K)
      (cong ((g⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) w) = w := by
    rw [← CFSG.RankThree.PartOne.K159.Klein.cong_coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, CFSG.RankThree.PartOne.K159.Klein.cong_one]
  rw [sum_cong_transpose_mul]
  have h1 := polar_quadPlus_three v
    (cong ((g⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) w)
  have h2 := polar_quadPlus_three (cong (g : Matrix (Fin 4) (Fin 4) K) v) w
  rw [← h1, ← h2, ← hpol, hinv]

end KleinFacts

section PSLFour

open CFSG.LocalAnalysis.ComponentInitial

variable (K : Type*) [Field K] [CharP K 2]

theorem scalars_four_eq_bot_of_charTwo : LinearFlag.scalars 4 K = ⊥ := by
  rw [eq_bot_iff]
  rintro A ⟨c, hc, hA⟩
  rw [Subgroup.mem_bot]
  have hc1 : (c : K) = 1 := by
    have h4 : (c : K) ^ 4 = 1 := by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
    have h : ((c : K) + 1) ^ 4 = 0 := by
      have e : ((c : K) + 1) ^ 4 = ((c : K) ^ 4 + 1) + 2 * (2 * (c : K) ^ 3 +
          3 * (c : K) ^ 2 + 2 * (c : K)) := by ring
      rw [e, h4, CharTwo.two_eq_zero, zero_mul, add_zero, CharTwo.add_self_eq_zero]
    exact CharTwo.add_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.mp h)
  apply Subtype.ext
  change (A : Matrix (Fin 4) (Fin 4) K) = 1
  rw [hA, hc1, map_one]

@[expose] noncomputable def pslFourEquivSL :
    LinearFlag.projectiveSL 4 K ≃* SpecialLinearGroup (Fin 4) K :=
  (QuotientGroup.quotientMulEquivOfEq (scalars_four_eq_bot_of_charTwo K)).trans
    QuotientGroup.quotientBot

variable {K}

end PSLFour

section Model

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (fieldAutT fieldAutT_mk
  matrixDerivedConjugation_fieldPair_val)

variable {K : Type} [Field K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

@[expose] noncomputable def kleinRep (E : Q.IsometryEquiv (quadPlus 3 K)) :
    SpecialLinearGroup (Fin 4) K →* ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
  CFSG.RankThree.PartOne.KCOrthogonal.transportHom E CFSG.RankThree.PartOne.K159.Klein.rho

theorem kleinRep_apply (E : Q.IsometryEquiv (quadPlus 3 K)) (g : SpecialLinearGroup (Fin 4) K)
    (v : Fin d → K) : E (kleinRep E g v) = cong (g : Matrix (Fin 4) (Fin 4) K) (E v) :=
  CFSG.RankThree.PartOne.KCOrthogonal.transportHom_apply E _ g v

theorem kleinRep_injective (E : Q.IsometryEquiv (quadPlus 3 K)) :
    Function.Injective (kleinRep E) :=
  CFSG.RankThree.PartOne.KCOrthogonal.transportHom_injective E _
    CFSG.RankThree.PartOne.K159.Klein.rho_injective

theorem kleinRep_mem_orthogonalGroup (E : Q.IsometryEquiv (quadPlus 3 K))
    (g : SpecialLinearGroup (Fin 4) K) : kleinRep E g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  CFSG.RankThree.PartOne.KCOrthogonal.transportHom_mem E _
    CFSG.RankThree.PartOne.K159.Klein.rho_mem g

variable [Finite K]

theorem kleinRep_range (E : Q.IsometryEquiv (quadPlus 3 K)) :
    (kleinRep E).range = orthDerived Q := by
  obtain ⟨hs, hp⟩ := CFSG.RankThree.PartOne.K159.Klein.sl4_isSimpleGroup_and_perfect (K := K)
  have hcard : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) =
      2 * Nat.card (SpecialLinearGroup (Fin 4) K) := by
    rw [CFSG.Timmesfeld.ClassicalOrders.card_orthogonalGroup_congr E,
      CFSG.RankThree.PartOne.K159.Klein.card_orthogonalGroup_quadPlus_three]
  have hle : (kleinRep E).range ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨g, rfl⟩
    exact kleinRep_mem_orthogonalGroup E g
  obtain ⟨-, -, -, -, -, -, hcomm, -⟩ :=
    CFSG.RankThree.PartOne.KCOrthogonal.derived_of_index_two_model _ (kleinRep E)
      (kleinRep_injective E) hle hcard
  exact hcomm.symm

theorem kleinRep_mem (E : Q.IsometryEquiv (quadPlus 3 K)) (g : SpecialLinearGroup (Fin 4) K) :
    kleinRep E g ∈ orthDerived Q := by
  rw [← kleinRep_range E]
  exact ⟨g, rfl⟩

omit [CharP K 2] [Finite K] in
theorem exists_ne_zero_of_isometry (E : Q.IsometryEquiv (quadPlus 3 K)) : ∃ v, Q v ≠ 0 := by
  refine ⟨E.symm (Pi.single (.inl 0) 1 + Pi.single (.inr 0) 1), ?_⟩
  rw [QuadraticMap.IsometryEquiv.map_app, quadPlus_apply]
  simp [Pi.single_apply]

@[expose] noncomputable def kleinEquivOf (E : Q.IsometryEquiv (quadPlus 3 K)) :
    LinearFlag.projectiveSL 4 K ≃* matrixProjectiveDerived Q :=
  (pslFourEquivSL K).trans ((MonoidHom.ofInjective (kleinRep_injective E)).trans
    ((MulEquiv.subgroupCongr (kleinRep_range E)).trans
      (MulEquiv.ofBijective (projHom Q)
        ⟨projHom_injective (exists_ne_zero_of_isometry E), projHom_surjective Q⟩)))

theorem kleinEquivOf_proj (E : Q.IsometryEquiv (quadPlus 3 K)) (g : SpecialLinearGroup (Fin 4) K) :
    kleinEquivOf E (LinearFlag.proj 4 K g) = projHom Q ⟨kleinRep E g, kleinRep_mem E g⟩ :=
  rfl

omit [CharP K 2] [Finite K] in
theorem fieldAutT_projHom (σ : K ≃+* K)
    (hQσ : ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v)) {ω ω' : orthDerived Q}
    (h : ∀ v, (ω' : (Fin d → K) ≃ₗ[K] (Fin d → K)) (coordinateFieldMap d σ v) =
      coordinateFieldMap d σ ((ω : (Fin d → K) ≃ₗ[K] (Fin d → K)) v)) :
    fieldAutT Q σ hQσ (projHom Q ω) = projHom Q ω' := by
  change fieldAutT Q σ hQσ (matrixProjectiveProjection Q ((derivedEquiv Q).symm ω)) =
    matrixProjectiveProjection Q ((derivedEquiv Q).symm ω')
  rw [fieldAutT_mk]
  congr 1
  apply (derivedEquiv Q).injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [coe_derivedEquiv, matrixDerivedConjugation_fieldPair_val]
  refine LinearEquiv.ext fun u => ?_
  obtain ⟨v, rfl⟩ := (coordinateFieldMap d σ).surjective u
  have h1 := coordinateFieldMap_matrix σ ((derivedEquiv Q).symm ω).val v
  have h2 : matrixLinearEquiv ((derivedEquiv Q).symm ω).val = (ω : _ ≃ₗ[K] _) := by
    have := coe_derivedEquiv Q ((derivedEquiv Q).symm ω)
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm
  change matrixLinearEquiv
    (CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut (Fin d) K σ
      ((derivedEquiv Q).symm ω).val)
    (coordinateFieldMap d σ v) = _
  rw [← h1, h2, h]

theorem kleinEquivOf_fieldAut (E : Q.IsometryEquiv (quadPlus 3 K)) (σ : K ≃+* K)
    (hE : ∀ v, E (coordinateFieldMap d σ v) = fun s => σ (E v s))
    (hQσ : ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v)) (x : LinearFlag.projectiveSL 4 K) :
    kleinEquivOf E (LinearFlag.fieldAut 4 K σ x) = fieldAutT Q σ hQσ (kleinEquivOf E x) := by
  obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective 4 K x
  rw [LinearFlag.fieldAut_proj, kleinEquivOf_proj, kleinEquivOf_proj]
  symm
  apply fieldAutT_projHom
  intro v
  apply EquivLike.injective E
  change E (kleinRep E _ _) = E (coordinateFieldMap d σ (kleinRep E g v))
  rw [kleinRep_apply, hE, hE, kleinRep_apply]
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  exact cong_map σ.toRingHom _ _

theorem kleinEquivOf_graphField (E : Q.IsometryEquiv (quadPlus 3 K)) (σ : K ≃+* K)
    (hE : ∀ v, E (coordinateFieldMap d σ v) = fun s => σ (E v s.swap))
    (hQσ : ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v)) (x : LinearFlag.projectiveSL 4 K) :
    kleinEquivOf E ((LinearFlag.fieldAut 4 K σ * LinearFlag.dualAut 4 K) x) =
      fieldAutT Q σ hQσ (kleinEquivOf E x) := by
  obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective 4 K x
  rw [MulAut.mul_apply, LinearFlag.dualAut_proj, LinearFlag.fieldAut_proj, kleinEquivOf_proj,
    kleinEquivOf_proj]
  symm
  apply fieldAutT_projHom
  intro v
  apply EquivLike.injective E
  change E (kleinRep E _ _) = E (coordinateFieldMap d σ (kleinRep E g v))
  rw [kleinRep_apply, hE, hE, kleinRep_apply]
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.SpecialLinearGroup.coe_transpose]
  have h1 := cong_map σ.toRingHom
    (((g⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ) (fun s => E v s.swap)
  rw [cong_inverseTranspose_star g (E v)] at h1
  exact h1

end Model

end CFSG.SeitzReduction.OmegaPilot
