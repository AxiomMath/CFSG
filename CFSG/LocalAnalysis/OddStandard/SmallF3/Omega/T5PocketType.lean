module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaInvol
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesCplxConj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2GenRefl
public import TauCeti.LinearAlgebra.QuadraticForm.CartanDieudonne.SpecialOrthogonal
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.Prod
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open TauCeti QuadraticMap CFSG.ClassicalInvolution

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

private abbrev P2 := Fin 2 → ZMod 3

private abbrev Q2 : QuadraticForm (ZMod 3) P2 :=
  presentedForm (⟨2, fun _ : Fin 2 => (1 : (ZMod 3)ˣ)⟩ : RegularFormPresentation (ZMod 3))

private lemma Q2_nondegenerate : Q2.Nondegenerate := by
  show (presentedForm (⟨2, fun _ : Fin 2 => (1 : (ZMod 3)ˣ)⟩ :
    RegularFormPresentation (ZMod 3))).Nondegenerate
  exact nondegenerate_presentedForm _

private lemma Q2_apply (x : P2) : Q2 x = x 0 * x 0 + x 1 * x 1 := by
  rw [presentedForm_apply, Fin.sum_univ_two]
  simp

private noncomputable def rot2 : P2 ≃ₗ[ZMod 3] P2 where
  toFun x := fun i => if i = 0 then x 1 else - x 0
  invFun x := fun i => if i = 0 then - x 1 else x 0
  left_inv x := by funext i; fin_cases i <;> simp
  right_inv x := by funext i; fin_cases i <;> simp
  map_add' x y := by funext i; fin_cases i <;> simp [neg_add, add_comm]
  map_smul' a x := by funext i; fin_cases i <;> simp

private lemma rot2_apply_zero (x : P2) : rot2 x 0 = x 1 := by
  change (if (0 : Fin 2) = 0 then x 1 else - x 0) = x 1
  simp

private lemma rot2_apply_one (x : P2) : rot2 x 1 = - x 0 := by
  change (if (1 : Fin 2) = 0 then x 1 else - x 0) = - x 0
  simp

private lemma rot2_mem : rot2 ∈ TauCeti.QuadraticMap.orthogonalGroup Q2 := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro x
  rw [Q2_apply (rot2 x), Q2_apply x, rot2_apply_zero, rot2_apply_one]
  ring

private noncomputable def p2 : OGroup Q2 := ⟨rot2, rot2_mem⟩

private lemma p2_sq : p2 * p2 = piOrth Q2 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;>
    simp only [p2, Subgroup.coe_mul, LinearEquiv.mul_apply, rot2_apply_zero, rot2_apply_one,
      coe_piOrth_apply, Pi.neg_apply]
  · rfl
  · rfl

private noncomputable def planeA : P2 := ![1, -1]

private noncomputable def planeB : P2 := ![0, 1]

@[simp] private lemma planeA_apply_zero : planeA 0 = 1 := by simp [planeA]

@[simp] private lemma planeA_apply_one : planeA 1 = -1 := by simp [planeA]

@[simp] private lemma planeB_apply_zero : planeB 0 = 0 := by simp [planeB]

@[simp] private lemma planeB_apply_one : planeB 1 = 1 := by simp [planeB]

private lemma Q2_planeA : Q2 planeA = (-1 : ZMod 3) := by
  rw [Q2_apply]
  decide

private lemma Q2_planeB : Q2 planeB = (1 : ZMod 3) := by
  rw [Q2_apply]
  decide

private lemma planeA_ne_zero : Q2 planeA ≠ 0 := by
  rw [Q2_planeA]; decide

private lemma planeB_ne_zero : Q2 planeB ≠ 0 := by
  rw [Q2_planeB]; decide

private lemma coe_reflOf_apply' (u : P2) (hu : Q2 u ≠ 0) (x : P2) :
    ((reflOf Q2 u hu : OGroup Q2) : P2 ≃ₗ[ZMod 3] P2) x =
      x - (QuadraticMap.polar Q2 u x / Q2 u) • u := by
  letI : Invertible (Q2 u) := invertibleOfNonzero hu
  rw [reflOf_eq u hu, TauCeti.QuadraticMap.coe_reflectionOrthogonal]
  exact TauCeti.QuadraticMap.reflection_apply_eq_sub_div Q2 u x

private lemma polar_Q2 (v x : P2) :
    QuadraticMap.polar Q2 v x = - (v 0 * x 0 + v 1 * x 1) := by
  rw [QuadraticMap.polar, Q2_apply (v + x), Q2_apply v, Q2_apply x]
  simp only [Pi.add_apply]
  ring_nf
  rw [show (2 : ZMod 3) = -1 from by decide]
  ring

private lemma p2_eq_refl_zero (x : P2) :
    rot2 x 0 = ((reflOf Q2 planeB planeB_ne_zero *
      reflOf Q2 planeA planeA_ne_zero : OGroup Q2) : P2 ≃ₗ[ZMod 3] P2) x 0 := by
  rw [Subgroup.coe_mul, LinearEquiv.mul_apply, coe_reflOf_apply' planeB planeB_ne_zero,
    coe_reflOf_apply' planeA planeA_ne_zero, rot2_apply_zero]
  simp only [Pi.sub_apply, Pi.smul_apply, polar_Q2, Q2_planeA, Q2_planeB, planeA_apply_zero,
    planeA_apply_one, planeB_apply_zero, planeB_apply_one, smul_eq_mul]
  ring_nf

private lemma p2_eq_refl_one (x : P2) :
    rot2 x 1 = ((reflOf Q2 planeB planeB_ne_zero *
      reflOf Q2 planeA planeA_ne_zero : OGroup Q2) : P2 ≃ₗ[ZMod 3] P2) x 1 := by
  rw [Subgroup.coe_mul, LinearEquiv.mul_apply, coe_reflOf_apply' planeB planeB_ne_zero,
    coe_reflOf_apply' planeA planeA_ne_zero, rot2_apply_one]
  simp only [Pi.sub_apply, Pi.smul_apply, polar_Q2, Q2_planeA, Q2_planeB, planeA_apply_zero,
    planeA_apply_one, planeB_apply_zero, planeB_apply_one, smul_eq_mul]
  ring_nf
  rw [show (2 : ZMod 3) = -1 from by decide]
  ring

private lemma p2_eq_refl :
    p2 = reflOf Q2 planeB planeB_ne_zero * reflOf Q2 planeA planeA_ne_zero := by
  apply Subtype.ext
  change rot2 = ((reflOf Q2 planeB planeB_ne_zero *
    reflOf Q2 planeA planeA_ne_zero : OGroup Q2) : P2 ≃ₗ[ZMod 3] P2)
  rw [Subgroup.coe_mul]
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i
  · exact p2_eq_refl_zero x
  · exact p2_eq_refl_one x

private lemma detSpinorNorm_reflOf_planeA :
    detSpinorNorm Q2_nondegenerate (reflOf Q2 planeA planeA_ne_zero) =
      ((-1 : (ZMod 3)ˣ), Multiplicative.ofAdd (squareClass (-1 : (ZMod 3)ˣ))) := by
  letI : Invertible (Q2 planeA) := invertibleOfNonzero planeA_ne_zero
  rw [reflOf_eq planeA planeA_ne_zero, detSpinorNorm_reflectionOrthogonal]
  have hunit : unitOfInvertible (Q2 planeA) = (-1 : (ZMod 3)ˣ) := by
    apply Units.ext
    rw [val_unitOfInvertible, Q2_planeA]
    simp
  rw [hunit, squareClassHom_apply]

private lemma detSpinorNorm_reflOf_planeB :
    detSpinorNorm Q2_nondegenerate (reflOf Q2 planeB planeB_ne_zero) =
      ((-1 : (ZMod 3)ˣ), (1 : Multiplicative (SquareClassGroup (ZMod 3)))) := by
  letI : Invertible (Q2 planeB) := invertibleOfNonzero planeB_ne_zero
  rw [reflOf_eq planeB planeB_ne_zero, detSpinorNorm_reflectionOrthogonal]
  have hunit : unitOfInvertible (Q2 planeB) = 1 := by
    apply Units.ext
    rw [val_unitOfInvertible, Q2_planeB]
    simp
  rw [hunit, map_one]

private lemma negClass_sq :
    Multiplicative.ofAdd (squareClass (-1 : (ZMod 3)ˣ)) ^ 2 = 1 := by
  rw [pow_two, ← ofAdd_add]
  have h : squareClass (-1 : (ZMod 3)ˣ) + squareClass (-1 : (ZMod 3)ˣ) = 0 := by
    rw [← squareClass_mul, show (-1 : (ZMod 3)ˣ) * (-1) = 1 from by decide]
    exact (squareClass_eq_zero_iff _).mpr ⟨1, by simp⟩
  rw [h, ofAdd_zero]

private lemma detSpinorNorm_p2 :
    detSpinorNorm Q2_nondegenerate p2 =
      (1, Multiplicative.ofAdd (squareClass (-1 : (ZMod 3)ˣ))) := by
  rw [p2_eq_refl, map_mul, detSpinorNorm_reflOf_planeB, detSpinorNorm_reflOf_planeA,
    Prod.mk_mul_mk, show (-1 : (ZMod 3)ˣ) * (-1) = 1 from by decide, one_mul]

private abbrev M := P2 × (P2 × P2)

private abbrev QM : QuadraticForm (ZMod 3) M := Q2.prod (Q2.prod Q2)

private abbrev QM_nondegenerate : QM.Nondegenerate :=
  Q2_nondegenerate.prod (Q2_nondegenerate.prod Q2_nondegenerate)

private lemma Q2_sign : quadSign Q2 = (-1 : ℤˣ) := by
  rw [quadSign_eq_signOf _ (nondegenerate_presentedForm _), TauCeti.formClass_presentedForm,
    signOf_mk_diag]
  simp

private lemma QM_sign : quadSign QM = (-1 : ℤˣ) := by
  rw [quadSign_prod Q2_nondegenerate (Q2_nondegenerate.prod Q2_nondegenerate),
    quadSign_prod Q2_nondegenerate Q2_nondegenerate, Q2_sign]
  simp only [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  decide

private lemma M_finrank : Module.finrank (ZMod 3) M = 6 := by
  change Module.finrank (ZMod 3) (P2 × (P2 × P2)) = 6
  rw [Module.finrank_prod, Module.finrank_prod]
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

private lemma piOrth_prod {W₁ W₂ : Type} [AddCommGroup W₁] [Module (ZMod 3) W₁]
    [FiniteDimensional (ZMod 3) W₁] [AddCommGroup W₂] [Module (ZMod 3) W₂]
    [FiniteDimensional (ZMod 3) W₂] {R₁ : QuadraticForm (ZMod 3) W₁}
    {R₂ : QuadraticForm (ZMod 3) W₂} :
    QuadraticMap.orthogonalGroupProd R₁ R₂ (piOrth R₁, piOrth R₂) =
      piOrth (R₁.prod R₂) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  rintro ⟨x₁, x₂⟩
  rw [QuadraticMap.orthogonalGroupProd_apply, coe_piOrth_apply, coe_piOrth_apply,
    coe_piOrth_apply]
  rfl

private lemma detSpinorNorm_orthogonalGroupProd {W₁ W₂ : Type} [AddCommGroup W₁]
    [Module (ZMod 3) W₁] [FiniteDimensional (ZMod 3) W₁] [AddCommGroup W₂]
    [Module (ZMod 3) W₂] [FiniteDimensional (ZMod 3) W₂] {R₁ : QuadraticForm (ZMod 3) W₁}
    {R₂ : QuadraticForm (ZMod 3) W₂} (hR₁ : R₁.Nondegenerate) (hR₂ : R₂.Nondegenerate)
    (g : OGroup R₁ × OGroup R₂) :
    detSpinorNorm (hR₁.prod hR₂)
      (QuadraticMap.orthogonalGroupProd R₁ R₂ g) =
      detSpinorNorm hR₁ g.1 * detSpinorNorm hR₂ g.2 := by
  rw [detSpinorNorm_apply, detSpinorNorm_apply, detSpinorNorm_apply,
    QuadraticMap.orthogonalDet_apply, QuadraticMap.orthogonalDet_apply,
    QuadraticMap.orthogonalDet_apply, QuadraticMap.det_orthogonalGroupProd,
    CliffordAlgebra.orthogonalSpinorNorm_orthogonalGroupProd]
  rfl

private noncomputable def pM : OGroup QM :=
  QuadraticMap.orthogonalGroupProd Q2 (Q2.prod Q2)
    (p2, QuadraticMap.orthogonalGroupProd Q2 Q2 (p2, p2))

private lemma pM_sq : pM * pM = piOrth QM := by
  rw [pM, ← map_mul]
  have h : (p2, QuadraticMap.orthogonalGroupProd Q2 Q2 (p2, p2)) *
      (p2, QuadraticMap.orthogonalGroupProd Q2 Q2 (p2, p2)) =
      (piOrth Q2, piOrth (Q2.prod Q2)) := by
    rw [Prod.mk_mul_mk, p2_sq]
    rw [← map_mul, Prod.mk_mul_mk, p2_sq]
    rw [piOrth_prod]
  rw [h, piOrth_prod]

private lemma detSpinorNorm_pM :
    detSpinorNorm QM_nondegenerate pM =
      (1, Multiplicative.ofAdd (squareClass (-1 : (ZMod 3)ˣ))) := by
  rw [pM, detSpinorNorm_orthogonalGroupProd Q2_nondegenerate
    (Q2_nondegenerate.prod Q2_nondegenerate)]
  rw [detSpinorNorm_p2]
  rw [detSpinorNorm_orthogonalGroupProd Q2_nondegenerate Q2_nondegenerate]
  rw [detSpinorNorm_p2]
  simp only [Prod.mk_mul_mk]
  refine Prod.ext ?_ ?_
  · simp
  · dsimp only
    rw [← pow_two, negClass_sq, mul_one]

private lemma detSpinorNorm_pM_ne_one :
    detSpinorNorm QM_nondegenerate pM ≠ 1 := by
  rw [detSpinorNorm_pM]
  intro h
  have h2 : Multiplicative.ofAdd (squareClass (-1 : (ZMod 3)ˣ)) = 1 := by
    simpa using congrArg Prod.snd h
  have h3 : squareClass (-1 : (ZMod 3)ˣ) = 0 := by
    have := congrArg Multiplicative.toAdd h2
    simpa using this
  exact aux_squareClass_neg_one_ne_zero h3

private lemma congr_piOrth {W : Type} [AddCommGroup W] [Module (ZMod 3) W]
    [FiniteDimensional (ZMod 3) W] {Q' : QuadraticForm (ZMod 3) W}
    (e : Q.IsometryEquiv Q') :
    TauCeti.QuadraticMap.orthogonalGroupCongr e (piOrth Q) = piOrth Q' := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rw [TauCeti.QuadraticMap.coe_orthogonalGroupCongr_apply, coe_piOrth_apply, coe_piOrth_apply]
  simp

private lemma detSpinorNorm_orthogonalGroupCongr {W : Type} [AddCommGroup W]
    [Module (ZMod 3) W] [FiniteDimensional (ZMod 3) W] {Q' : QuadraticForm (ZMod 3) W}
    (e : Q.IsometryEquiv Q') (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate) (g : OGroup Q) :
    detSpinorNorm hQ' (TauCeti.QuadraticMap.orthogonalGroupCongr e g) =
      detSpinorNorm hQ g := by
  have key : (detSpinorNorm hQ').comp
      (TauCeti.QuadraticMap.orthogonalGroupCongr e).toMonoidHom = detSpinorNorm hQ := by
    refine TauCeti.QuadraticMap.orthogonalGroup_hom_ext Q hQ fun v hv => ?_
    haveI : Invertible (Q' (e v)) := by rw [e.map_app]; exact hv
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      TauCeti.QuadraticMap.orthogonalGroupCongr_reflectionOrthogonal,
      detSpinorNorm_reflectionOrthogonal, detSpinorNorm_reflectionOrthogonal]
    exact Prod.ext rfl (congrArg squareClassHom
      (Units.ext (by rw [val_unitOfInvertible, val_unitOfInvertible, e.map_app])))
  exact DFunLike.congr_fun key g

theorem t5_pi_not_sq (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1) :
    ¬ ∃ p : omegaGroup hQ, (p : OGroup Q) * p = piOrth Q := by
  rintro ⟨p, hp⟩
  set P : OGroup Q := (p : OGroup Q) with hPdef
  have hPpi : P * P = piOrth Q := hp
  have hPdet : detSpinorNorm hQ P = 1 := (mem_omegaGroup_iff hQ).mp p.2
  have hdimM : Module.finrank (ZMod 3) V = Module.finrank (ZMod 3) M := by
    rw [hdim, M_finrank]
  have hsignM : quadSign Q = quadSign QM := by rw [hs, QM_sign]
  obtain ⟨e⟩ := equivalent_of_quadSign_eq hQ QM_nondegenerate hdimM hsignM
  let P' : OGroup QM := TauCeti.QuadraticMap.orthogonalGroupCongr e P
  have hP'pi : P' * P' = piOrth QM := by
    rw [show P' * P' = TauCeti.QuadraticMap.orthogonalGroupCongr e (P * P) from
      (map_mul _ _ _).symm, hPpi, congr_piOrth e]
  have hP'det : detSpinorNorm QM_nondegenerate P' = 1 := by
    rw [detSpinorNorm_orthogonalGroupCongr e hQ QM_nondegenerate P, hPdet]
  have hconj := isConj_of_mul_self_eq_piOrth QM_nondegenerate hP'pi pM_sq
  rw [isConj_iff] at hconj
  obtain ⟨g, hg⟩ := hconj
  have hP'Ω : P' ∈ omegaGroup QM_nondegenerate :=
    (mem_omegaGroup_iff QM_nondegenerate).mpr hP'det
  have hpMΩ : pM ∈ omegaGroup QM_nondegenerate := by
    rw [← hg]
    exact (omegaGroup_normal QM_nondegenerate).conj_mem P' hP'Ω g
  exact detSpinorNorm_pM_ne_one ((mem_omegaGroup_iff QM_nondegenerate).mp hpMΩ)

theorem t5_omega_involution_type (hdim : Module.finrank (ZMod 3) V = 6)
    {g : OGroup Q} (hg : g * g = 1) (hgΩ : g ∈ omegaGroup hQ) :
    invType g = (0, 1) ∨ invType g = (2, -1) ∨ invType g = (4, 1) ∨ invType g = (6, -1) := by
  obtain ⟨hEven, hsign⟩ := (involution_mem_omegaGroup_iff hQ hg).mp hgΩ
  obtain ⟨k, hk⟩ := hEven
  have hle : invDim g ≤ 6 := by rw [← hdim]; exact invDim_le g
  have hk3 : k ≤ 3 := by omega
  interval_cases k
  · left
    have hd : invDim g = 0 := by omega
    have hs : invSign g = (1 : ℤˣ) := by rw [hsign, hd]; decide
    simp only [invType]
    rw [hd, hs]
  · right; left
    have hd : invDim g = 2 := by omega
    have hs : invSign g = (-1 : ℤˣ) := by rw [hsign, hd]; decide
    simp only [invType]
    rw [hd, hs]
  · right; right; left
    have hd : invDim g = 4 := by omega
    have hs : invSign g = (1 : ℤˣ) := by rw [hsign, hd]; decide
    simp only [invType]
    rw [hd, hs]
  · right; right; right
    have hd : invDim g = 6 := by omega
    have hs : invSign g = (-1 : ℤˣ) := by rw [hsign, hd]; decide
    simp only [invType]
    rw [hd, hs]

end CFSG.OddStandard.SmallF3.Omega
