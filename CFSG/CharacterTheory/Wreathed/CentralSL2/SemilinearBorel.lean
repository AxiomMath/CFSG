module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.SemilinearClifford
public import CFSG.CharacterTheory.Wreathed.CentralSL2.SemilinearInvolutionClasses
public import CFSG.CharacterTheory.Wreathed.CentralSL2.InductionTools

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization
open TwoRankLowerBound.Helpers

section Elements

variable {F : Type} [Field F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

theorem fieldSL_diagSL (σ : F ≃+* F) (c : Fˣ) :
    fieldSL F σ (diagSL F c) = diagSL F (Units.map σ.toRingHom.toMonoidHom c) := by
  apply SL_eq_of_val
  ext i j
  change σ ((diagSL F c : SpecialLinearGroup (Fin 2) F) i j) =
    (diagSL F (Units.map σ.toRingHom.toMonoidHom c) : SpecialLinearGroup (Fin 2) F) i j
  rw [diagSL_val, diagSL_val]
  fin_cases i <;> fin_cases j <;> simp

theorem fieldSL_upperSL (σ : F ≃+* F) (t : F) : fieldSL F σ (upperSL F t) = upperSL F (σ t) := by
  apply SL_eq_of_val
  ext i j
  change σ ((upperSL F t : SpecialLinearGroup (Fin 2) F) i j) =
    (upperSL F (σ t) : SpecialLinearGroup (Fin 2) F) i j
  rw [upperSL_val, upperSL_val]
  fin_cases i <;> fin_cases j <;> simp

theorem fieldAction_torusDiag (σ : Sigma) (c : Fˣ) :
    fieldAction F b m hm heven Sigma hSigma σ (torusDiag F b m hm heven c) =
      torusDiag F b m hm heven (Units.map (σ : F ≃+* F).toRingHom.toMonoidHom c) := by
  rw [torusDiag, fieldAction_specialInclusion, fieldSL_diagSL, torusDiag]

theorem fieldAction_unipotentElement (σ : Sigma) (t : F) :
    fieldAction F b m hm heven Sigma hSigma σ (unipotentElement F b m hm heven t) =
      unipotentElement F b m hm heven ((σ : F ≃+* F) t) := by
  rw [unipotentElement, fieldAction_specialInclusion, fieldSL_upperSL, unipotentElement]

theorem fieldAction_weylElement (σ : Sigma) :
    fieldAction F b m hm heven Sigma hSigma σ (weylElement F b m hm heven) =
      weylElement F b m hm heven := by
  rw [weylElement, fieldAction_specialInclusion, fieldSL_weyl]

theorem fieldAction_torusGenerator (σ : Sigma) :
    fieldAction F b m hm heven Sigma hSigma σ (torusGenerator F b m hm heven) =
      torusGenerator F b m hm heven := by
  rw [torusGenerator, map_mul, map_inv, fieldAction_weylElement, fieldAction_cyclicGenerator]

theorem fieldAction_smul (σ : Sigma) (g : CentralExtension F b m hm heven) (x : Omega F) :
    fieldAction F b m hm heven Sigma hSigma σ g • x =
      fieldExtension F (σ : F ≃+* F) (g • (fieldExtension F (σ : F ≃+* F)).symm x) := by
  rw [centralExtension_smul_def, projAction_fieldAction, centralExtension_smul_def]
  rfl

theorem fieldAction_smul_none (σ : Sigma) (g : CentralExtension F b m hm heven) :
    fieldAction F b m hm heven Sigma hSigma σ g • (none : Omega F) = none ↔
      g • (none : Omega F) = none := by
  rw [fieldAction_smul]
  have h1 : (fieldExtension F (σ : F ≃+* F)).symm (none : Omega F) = none := by
    rw [Equiv.symm_apply_eq]
    rfl
  rw [h1]
  constructor
  · intro h
    have := congrArg (fieldExtension F (σ : F ≃+* F)).symm h
    rwa [Equiv.symm_apply_apply, h1] at this
  · intro h
    rw [h]
    rfl

theorem fieldAction_smul_zero (σ : Sigma) (g : CentralExtension F b m hm heven) :
    fieldAction F b m hm heven Sigma hSigma σ g • (some 0 : Omega F) = some 0 ↔
      g • (some 0 : Omega F) = some 0 := by
  rw [fieldAction_smul]
  have h1 : (fieldExtension F (σ : F ≃+* F)).symm (some 0 : Omega F) = some 0 := by
    rw [Equiv.symm_apply_eq]
    change some (0 : F) = some ((σ : F ≃+* F) 0)
    rw [map_zero]
  rw [h1]
  constructor
  · intro h
    have := congrArg (fieldExtension F (σ : F ≃+* F)).symm h
    rwa [Equiv.symm_apply_apply, h1] at this
  · intro h
    rw [h]
    change some ((σ : F ≃+* F) 0) = some 0
    rw [map_zero]

theorem fieldAction_mem_borel_iff (σ : Sigma) (g : CentralExtension F b m hm heven) :
    fieldAction F b m hm heven Sigma hSigma σ g ∈ borelSubgroup F b m hm heven ↔
      g ∈ borelSubgroup F b m hm heven := by
  rw [mem_borelSubgroup_iff, mem_borelSubgroup_iff]
  exact fieldAction_smul_none hSigma σ g

theorem fieldAction_mem_splitTorus_iff (σ : Sigma) (g : CentralExtension F b m hm heven) :
    fieldAction F b m hm heven Sigma hSigma σ g ∈ splitTorus F b m hm heven ↔
      g ∈ splitTorus F b m hm heven := by
  rw [mem_splitTorus_iff, mem_splitTorus_iff, fieldAction_smul_none hSigma,
    fieldAction_smul_zero hSigma]

theorem fieldAction_mem_unipotent_iff (σ : Sigma) (g : CentralExtension F b m hm heven) :
    fieldAction F b m hm heven Sigma hSigma σ g ∈ unipotentSubgroup F b m hm heven ↔
      g ∈ unipotentSubgroup F b m hm heven := by
  rw [mem_unipotentSubgroup_iff, mem_unipotentSubgroup_iff]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨(σ : F ≃+* F).symm t, ?_⟩
    apply (fieldAction F b m hm heven Sigma hSigma σ).injective
    rw [fieldAction_unipotentElement, RingEquiv.apply_symm_apply, ht]
  · rintro ⟨t, rfl⟩
    exact ⟨(σ : F ≃+* F) t, (fieldAction_unipotentElement hSigma σ t).symm⟩

theorem borelProjection_fieldAction (σ : Sigma) (g : borelSubgroup F b m hm heven) :
    (borelProjection F b m hm heven ⟨fieldAction F b m hm heven Sigma hSigma σ g,
      (fieldAction_mem_borel_iff hSigma σ (g : CentralExtension F b m hm heven)).mpr g.2⟩ :
        CentralExtension F b m hm heven) =
      fieldAction F b m hm heven Sigma hSigma σ (borelProjection F b m hm heven g) := by
  have hdec := unipotentElement_mul_borelProjectionFun F b m hm heven g
  have hu : fieldAction F b m hm heven Sigma hSigma σ
      (unipotentElement F b m hm heven (borelTranslation F b m hm heven g)) ∈
        unipotentSubgroup F b m hm heven :=
    (fieldAction_mem_unipotent_iff hSigma σ _).mpr
      ((mem_unipotentSubgroup_iff F b m hm heven _).mpr ⟨_, rfl⟩)
  have ht : fieldAction F b m hm heven Sigma hSigma σ (borelProjectionFun F b m hm heven g) ∈
      splitTorus F b m hm heven :=
    (fieldAction_mem_splitTorus_iff hSigma σ _).mpr (borelProjectionFun_mem F b m hm heven g.2)
  rw [borelProjection_apply, borelProjection_apply]
  apply borelProjectionFun_eq F b m hm heven hu ht
  change fieldAction F b m hm heven Sigma hSigma σ g = _
  rw [← map_mul, hdec]

end Elements

section Parameters

variable {F : Type} [Field F] {b : Fˣ} {m : ℕ}
  {Sigma : Subgroup (F ≃+* F)} (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

@[expose] noncomputable def unitsField (σ : F ≃+* F) : Fˣ →* Fˣ :=
  Units.map σ.toRingHom.toMonoidHom

theorem unitsField_apply (σ : F ≃+* F) (c : Fˣ) : ((unitsField σ c : Fˣ) : F) = σ c := rfl

include hSigma in
theorem unitsField_torusConstant (σ : Sigma) :
    unitsField (σ : F ≃+* F) (torusConstant F b m) = torusConstant F b m := by
  apply Units.ext
  rw [unitsField_apply, torusConstant]
  simp only [Units.val_neg, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, map_neg,
    map_pow, map_inv₀, hSigma σ σ.2]

include hSigma in
theorem unitsField_b (σ : Sigma) : unitsField (σ : F ≃+* F) b = b :=
  Units.ext (hSigma σ σ.2)

include hSigma in
@[expose] noncomputable def fieldParameter (σ : Sigma) (P : PrincipalSeriesParameter F b m) :
    PrincipalSeriesParameter F b m :=
  ⟨(P.1.1.comp (unitsField ((σ⁻¹ : Sigma) : F ≃+* F)), P.1.2), by
    rw [MonoidHom.comp_apply, unitsField_torusConstant hSigma σ⁻¹]
    exact P.2⟩

theorem fieldParameter_fst (σ : Sigma) (P : PrincipalSeriesParameter F b m) :
    (fieldParameter hSigma σ P).1 = (P.1.1.comp (unitsField ((σ⁻¹ : Sigma) : F ≃+* F)), P.1.2) :=
  rfl

theorem fieldParameter_one (P : PrincipalSeriesParameter F b m) :
    fieldParameter hSigma 1 P = P := by
  apply Subtype.ext
  refine Prod.ext (MonoidHom.ext fun c => ?_) rfl
  change P.1.1 (unitsField ((1⁻¹ : Sigma) : F ≃+* F) c) = P.1.1 c
  congr 1

theorem fieldParameter_mul (σ τ : Sigma) (P : PrincipalSeriesParameter F b m) :
    fieldParameter hSigma (σ * τ) P = fieldParameter hSigma σ (fieldParameter hSigma τ P) := by
  apply Subtype.ext
  refine Prod.ext (MonoidHom.ext fun c => ?_) rfl
  change P.1.1 (unitsField (((σ * τ)⁻¹ : Sigma) : F ≃+* F) c) =
    P.1.1 (unitsField ((τ⁻¹ : Sigma) : F ≃+* F) (unitsField ((σ⁻¹ : Sigma) : F ≃+* F) c))
  congr 1

theorem fieldParameter_weylParameter (heven : Even m) (σ : Sigma)
    (P : PrincipalSeriesParameter F b m) :
    fieldParameter hSigma σ (weylParameter F b m heven P) =
      weylParameter F b m heven (fieldParameter hSigma σ P) := by
  apply Subtype.ext
  refine Prod.ext (MonoidHom.ext fun c => rfl) ?_
  change P.1.1 b * P.1.2 = P.1.1 (unitsField ((σ⁻¹ : Sigma) : F ≃+* F) b) * P.1.2
  rw [unitsField_b hSigma σ⁻¹]

include hSigma in
@[expose] noncomputable def parameterStabilizer (P : PrincipalSeriesParameter F b m) :
    Subgroup Sigma where
  carrier := {σ | fieldParameter hSigma σ P = P}
  one_mem' := fieldParameter_one hSigma P
  mul_mem' := by
    intro σ τ hσ hτ
    simp only [Set.mem_ofPred_eq] at hσ hτ ⊢
    rw [fieldParameter_mul, hτ, hσ]
  inv_mem' := by
    intro σ hσ
    simp only [Set.mem_ofPred_eq] at hσ ⊢
    have h1 := fieldParameter_mul hSigma σ⁻¹ σ P
    rw [inv_mul_cancel, fieldParameter_one, hσ] at h1
    exact h1.symm

theorem mem_parameterStabilizer_iff (P : PrincipalSeriesParameter F b m) (σ : Sigma) :
    σ ∈ parameterStabilizer hSigma P ↔ fieldParameter hSigma σ P = P := Iff.rfl

theorem fieldParameter_pow (σ : Sigma) (n : ℕ) (P : PrincipalSeriesParameter F b m) :
    fieldParameter hSigma (σ ^ n) P = (fieldParameter hSigma σ)^[n] P := by
  induction n generalizing P with
  | zero => rw [pow_zero, fieldParameter_one, Function.iterate_zero_apply]
  | succ n ih => rw [pow_succ, fieldParameter_mul, Function.iterate_succ_apply, ih]

theorem fieldParameter_ne_weylParameter [Fintype F] (heven : Even m) (hb : ¬ IsSquare b)
    (hd : Odd (Nat.card Sigma)) (σ : Sigma) {P : PrincipalSeriesParameter F b m}
    (hP : P.1.1 ≠ 1) : fieldParameter hSigma σ P ≠ weylParameter F b m heven P := by
  intro h
  have hodd : Odd (orderOf σ) := Odd.of_dvd_nat hd (orderOf_dvd_natCard σ)
  have hiter : ∀ k : ℕ, (fieldParameter hSigma σ)^[2 * k + 1] P = weylParameter F b m heven P := by
    intro k
    induction k with
    | zero => simpa using h
    | succ k ih =>
      rw [show 2 * (k + 1) + 1 = 2 + (2 * k + 1) by ring, Function.iterate_add_apply, ih]
      show fieldParameter hSigma σ (fieldParameter hSigma σ (weylParameter F b m heven P)) = _
      rw [fieldParameter_weylParameter, h, weylParameter_involutive F b m heven P]
      exact h
  obtain ⟨k, hk⟩ := hodd
  have h1 := hiter k
  rw [← hk, ← fieldParameter_pow, pow_orderOf_eq_one, fieldParameter_one] at h1
  exact ne_weylParameter F b m heven hb hP h1

end Parameters

section Characters

variable {F : Type} [Field F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

@[expose] noncomputable def torusField (σ : Sigma) :
    splitTorus F b m hm heven →* splitTorus F b m hm heven where
  toFun t := ⟨fieldAction F b m hm heven Sigma hSigma σ t,
    (fieldAction_mem_splitTorus_iff hSigma σ (t : CentralExtension F b m hm heven)).mpr t.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

theorem torusCharacter_fieldAction (σ : Sigma) (P : PrincipalSeriesParameter F b m) :
    (torusCharacter F b m hm heven P).comp (torusField (hm := hm) (heven := heven) hSigma σ⁻¹) =
      torusCharacter F b m hm heven (fieldParameter hSigma σ P) := by
  apply splitTorusCharacter_unique
  · intro c
    rw [MonoidHom.comp_apply]
    have hc : torusField hSigma σ⁻¹
        ⟨torusDiag F b m hm heven c, torusDiag_mem_splitTorus F b m hm heven c⟩ =
          ⟨torusDiag F b m hm heven (unitsField ((σ⁻¹ : Sigma) : F ≃+* F) c),
            torusDiag_mem_splitTorus F b m hm heven _⟩ :=
      Subtype.ext (fieldAction_torusDiag hSigma σ⁻¹ c)
    rw [hc, torusCharacter_torusDiag]
    rfl
  · rw [MonoidHom.comp_apply]
    have hv : torusField hSigma σ⁻¹
        ⟨torusGenerator F b m hm heven, torusGenerator_mem_splitTorus F b m hm heven⟩ =
          ⟨torusGenerator F b m hm heven, torusGenerator_mem_splitTorus F b m hm heven⟩ :=
      Subtype.ext (fieldAction_torusGenerator hSigma σ⁻¹)
    rw [hv, torusCharacter_torusGenerator]
    rfl

theorem principalSeries_fieldTwist [Fintype F] (σ : Sigma) (P : PrincipalSeriesParameter F b m) :
    fieldTwist hSigma σ (principalSeries F b m hm heven (torusCharacter F b m hm heven P)) =
      principalSeries F b m hm heven
        (torusCharacter F b m hm heven (fieldParameter hSigma σ P)) := by
  funext g
  rw [fieldTwist_apply, principalSeries, inducedFunction_mulEquiv _ _
    (fieldAction_mem_borel_iff hSigma σ⁻¹), principalSeries]
  congr 1
  funext x
  change (torusCharacter F b m hm heven P (borelProjection F b m hm heven
    ⟨fieldAction F b m hm heven Sigma hSigma σ⁻¹ x, _⟩) : ℂ) =
      (torusCharacter F b m hm heven (fieldParameter hSigma σ P)
        (borelProjection F b m hm heven x) : ℂ)
  rw [← torusCharacter_fieldAction hSigma σ P, MonoidHom.comp_apply]
  congr 2
  exact Subtype.ext (borelProjection_fieldAction hSigma σ⁻¹ x)

theorem twistStabilizer_principalSeries [Fintype F] (hb : ¬ IsSquare b)
    (hd : Odd (Nat.card Sigma)) {P : PrincipalSeriesParameter F b m} (hP : P.1.1 ≠ 1) :
    twistStabilizer hSigma (principalSeries F b m hm heven (torusCharacter F b m hm heven P)) =
      parameterStabilizer hSigma P := by
  ext σ
  rw [mem_twistStabilizer_iff, principalSeries_fieldTwist, mem_parameterStabilizer_iff]
  have hσP : (fieldParameter hSigma σ P).1.1 ≠ 1 := by
    intro h
    apply hP
    refine MonoidHom.ext fun c => ?_
    have h1 := DFunLike.congr_fun h (unitsField ((σ : Sigma) : F ≃+* F) c)
    change P.1.1 (unitsField ((σ⁻¹ : Sigma) : F ≃+* F)
      (unitsField ((σ : Sigma) : F ≃+* F) c)) = 1 at h1
    rw [MonoidHom.one_apply, ← h1]
    congr 1
    apply Units.ext
    change c = (σ : F ≃+* F).symm ((σ : F ≃+* F) c)
    rw [RingEquiv.symm_apply_apply]
  constructor
  · intro h
    rcases (principalSeries_eq_iff F b m hm heven hb hσP hP).mp h with h1 | h1
    · exact h1.symm
    · exfalso
      have h2 : weylParameter F b m heven P = fieldParameter hSigma σ P :=
        (congrArg (weylParameter F b m heven) h1).trans (weylParameter_involutive F b m heven _)
      exact fieldParameter_ne_weylParameter hSigma heven hb hd σ hP h2.symm
  · intro h
    rw [h]

end Characters

end CFSG.Wreathed.CentralSL2
