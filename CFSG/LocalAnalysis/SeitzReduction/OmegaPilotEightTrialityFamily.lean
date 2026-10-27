module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightTrialityAut

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Matrix
open CFSG.LieType.Steinberg CFSG.LieType.Universal.Spin
open CFSG.LieType.RootSystem (roots)
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus StatedProj StatedScalars)
open CFSG.ClassicalGroups.Orthogonal (toLinEquiv toLinEquiv_apply)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus
  projectivePointFamily)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction (Points pointMk pointMk_eq_iff
  exists_eq_pointMk statedPointAction statedOrthogonalHom orthogonalPointAction_pointMk)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedPointStabilizer statedPointFamily mem_statedPointStabilizer_iff)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit (plusCoordinateEquiv
  plusCoordinate_pointFamily familyTransport familyTransport_automorphism)
open CFSG.ComponentClassification.CatalogueBStabilizerFamily (family pointStabilizer)
open scoped Pointwise

section Coordinates

theorem d4TrialityPerm_symm_apply :
    d4TrialityPerm.symm 0 = 3 ∧ d4TrialityPerm.symm 1 = 1 ∧ d4TrialityPerm.symm 2 = 0 ∧
      d4TrialityPerm.symm 3 = 2 := by decide

theorem toStdD_triality_zero (v : Fin 4 → ℤ) :
    2 * toStdD 4 (fundPerm d4TrialityPerm v) 0 =
      toStdD 4 v 0 + toStdD 4 v 1 + toStdD 4 v 2 + toStdD 4 v 3 := by
  simp [toStdD, fundPerm_apply, d4TrialityPerm_symm_apply.1]
  ring

theorem toStdD_triality_one (v : Fin 4 → ℤ) :
    2 * toStdD 4 (fundPerm d4TrialityPerm v) 1 =
      toStdD 4 v 0 + toStdD 4 v 1 - toStdD 4 v 2 - toStdD 4 v 3 := by
  simp [toStdD, fundPerm_apply, d4TrialityPerm_symm_apply.1, d4TrialityPerm_symm_apply.2.1]
  ring

theorem long_sum_nonneg : ∀ (i j : Fin 4) (s t : Bool), i ≠ j →
    (Pi.single i (boolSign s) + Pi.single j (boolSign t) : Fin 4 → ℤ) 0 = 1 →
      0 ≤ (Pi.single i (boolSign s) + Pi.single j (boolSign t) : Fin 4 → ℤ) 0 +
        (Pi.single i (boolSign s) + Pi.single j (boolSign t) : Fin 4 → ℤ) 1 +
        (Pi.single i (boolSign s) + Pi.single j (boolSign t) : Fin 4 → ℤ) 2 +
        (Pi.single i (boolSign s) + Pi.single j (boolSign t) : Fin 4 → ℤ) 3 := by decide

theorem long_diff_nonneg : ∀ (i j : Fin 4) (s t : Bool), i ≠ j →
    (Pi.single i (boolSign s) + Pi.single j (boolSign t) : Fin 4 → ℤ) 0 = 1 →
      0 ≤ (Pi.single i (boolSign s) + Pi.single j (boolSign t) : Fin 4 → ℤ) 0 +
        (Pi.single i (boolSign s) + Pi.single j (boolSign t) : Fin 4 → ℤ) 1 -
        (Pi.single i (boolSign s) + Pi.single j (boolSign t) : Fin 4 → ℤ) 2 -
        (Pi.single i (boolSign s) + Pi.single j (boolSign t) : Fin 4 → ℤ) 3 := by decide

variable {F : Type} [Field F] [CharP F 2]

theorem toStdD_triality_nonneg {γ : Fin 4 → ℤ} (hγ : γ ∈ (SpinPlus.Φ 4 F d4_three_le).roots)
    (h0 : toStdD 4 γ 0 = 1) :
    0 ≤ toStdD 4 (fundPerm d4TrialityPerm γ) 0 ∧ 0 ≤ toStdD 4 (fundPerm d4TrialityPerm γ) 1 := by
  obtain ⟨i, j, hij, s, t, he⟩ := exists_toStdD_eq_of_mem_roots hγ
  have hs := long_sum_nonneg i j s t hij (he ▸ h0)
  have hd := long_diff_nonneg i j s t hij (he ▸ h0)
  have e0 := toStdD_triality_zero γ
  have e1 := toStdD_triality_one γ
  rw [he] at e0 e1
  constructor <;> omega

end Coordinates

section Stated

open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction (orthogonalPointAction)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (automorphismTransport_symm_apply)

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem mk_mem_statedPointStabilizer_iff (A : StatedOmega (StatedQuadPlus 4 F))
    (w : Fin 4 ⊕ Fin 4 → F) (hw : w ≠ 0) (hQw : quadPlus 4 F w = 0) :
    QuotientGroup.mk' ((StatedScalars (Fin 4 ⊕ Fin 4) F).subgroupOf
        (StatedOmega (StatedQuadPlus 4 F))) A ∈
        statedPointStabilizer (coe_quadPlus 4 F) (pointMk w hw hQw) ↔
      ∃ a : F, a • w = (A : GL (Fin 4 ⊕ Fin 4) F).val *ᵥ w := by
  rw [mem_statedPointStabilizer_iff]
  change orthogonalPointAction (quadPlus 4 F) (statedOrthogonalHom (coe_quadPlus 4 F) A)
      (pointMk w hw hQw) = pointMk w hw hQw ↔ _
  rw [orthogonalPointAction_pointMk, pointMk_eq_iff]
  simp only [statedOrthogonalHom, MonoidHom.coe_mk, OneHom.coe_mk, toLinEquiv_apply]

theorem plusVec_true_ne_zero (m : Fin 4) : plusVec 4 F m true ≠ 0 := by
  intro h
  have h1 := congrFun h (Sum.inl m)
  simp [plusVec] at h1

variable (F) in
@[expose] noncomputable def pointE (m : Fin 4) : Points (quadPlus 4 F) :=
  pointMk (plusVec 4 F m true) (plusVec_true_ne_zero m) (quadPlus_plusVec 4 F m true)

theorem plusVec_true_plusIdx (m j : Fin 4) (r : Bool) :
    plusVec 4 F m true (SpinPlus.plusIdx j r) = if j = m ∧ r = true then 1 else 0 := by
  cases r <;> simp [plusVec, SpinPlus.plusIdx, Pi.single_apply]

theorem spinMatrix_x_mulVec_plusVec {γ : Fin 4 → ℤ} {i j : Fin 4} (hij : i ≠ j) {s t : Bool}
    (he : toStdD 4 γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) {m : Fin 4}
    (hm : 0 ≤ toStdD 4 γ m) (c : F) :
    (spinMatrix (quadPlus 4 F) (SpinPlus.x 4 F d4_three_le γ c) : Matrix _ _ F) *ᵥ
        plusVec 4 F m true = plusVec 4 F m true := by
  rw [spinMatrix_x_mulVec hij he, plusVec_true_plusIdx, plusVec_true_plusIdx]
  have h1 : ¬(j = m ∧ t = false) := by
    rintro ⟨rfl, rfl⟩
    rw [he] at hm
    simp [Ne.symm hij] at hm
  have h2 : ¬(i = m ∧ s = false) := by
    rintro ⟨rfl, rfl⟩
    rw [he] at hm
    simp [hij] at hm
  simp only [Bool.not_eq_true', h1, h2, ite_false, Pi.single_zero, smul_zero, add_zero]

theorem mk_x_mem_stab_pointE {γ : Fin 4 → ℤ} (hγ : γ ∈ (SpinPlus.Φ 4 F d4_three_le).roots)
    {m : Fin 4} (hm : 0 ≤ toStdD 4 γ m) (c : F) :
    QuotientGroup.mk' ((StatedScalars (Fin 4 ⊕ Fin 4) F).subgroupOf
        (StatedOmega (StatedQuadPlus 4 F))) (spin8OmegaEquiv F (SpinPlus.x 4 F d4_three_le γ c)) ∈
      statedPointStabilizer (coe_quadPlus 4 F) (pointE F m) := by
  obtain ⟨i, j, hij, s, t, he⟩ := exists_toStdD_eq_of_mem_roots hγ
  rw [pointE, mk_mem_statedPointStabilizer_iff]
  refine ⟨1, ?_⟩
  rw [one_smul, coe_spin8OmegaEquiv, spinMatrix_x_mulVec_plusVec hij he hm]

theorem coord_eq_zero_of_smul_eq {w : Fin 4 ⊕ Fin 4 → F} {a : F} {j : Fin 4} (hj : j ≠ 0)
    {t : Bool}
    (h : a • w = w + (1 : F) • (Pi.single (SpinPlus.plusIdx 0 true) (w (SpinPlus.plusIdx j (!t))) +
      Pi.single (SpinPlus.plusIdx j t) (w (SpinPlus.plusIdx 0 (!true))))) :
    w (SpinPlus.plusIdx j (!t)) = 0 ∧ w (Sum.inr 0) = 0 := by
  have hb0 : SpinPlus.plusIdx j (!t) ≠ Sum.inl 0 := by
    cases t <;> simp [SpinPlus.plusIdx, hj]
  have hbd : SpinPlus.plusIdx j (!t) ≠ SpinPlus.plusIdx j t := by
    cases t <;> simp [SpinPlus.plusIdx]
  have hdr : SpinPlus.plusIdx j t ≠ Sum.inr 0 := by
    cases t <;> simp [SpinPlus.plusIdx, hj]
  have hd0 : SpinPlus.plusIdx j t ≠ Sum.inl 0 := by
    cases t <;> simp [SpinPlus.plusIdx, hj]
  have hp0 : SpinPlus.plusIdx (0 : Fin 4) true = Sum.inl 0 := rfl
  have hp1 : SpinPlus.plusIdx (0 : Fin 4) (!true) = Sum.inr 0 := rfl
  have e1 := congrFun h (SpinPlus.plusIdx j (!t))
  have e2 := congrFun h (Sum.inr 0)
  have e3 := congrFun h (Sum.inl 0)
  have e4 := congrFun h (SpinPlus.plusIdx j t)
  simp only [hp0, hp1, Pi.smul_apply, Pi.add_apply, smul_eq_mul, one_mul, Pi.single_apply, hb0,
    hbd, hd0, Ne.symm hdr, Ne.symm hd0, ite_true, ite_false, add_zero, zero_add,
    reduceCtorEq] at e1 e2 e3 e4
  by_cases ha : a = 1
  · subst ha
    constructor
    · linear_combination -e3
    · linear_combination -e4
  · have ha' : a - 1 ≠ 0 := sub_ne_zero.2 ha
    constructor
    · have h3 : (a - 1) * w (SpinPlus.plusIdx j (!t)) = 0 := by linear_combination e1
      exact (mul_eq_zero.1 h3).resolve_left ha'
    · have h3 : (a - 1) * w (Sum.inr 0) = 0 := by linear_combination e2
      exact (mul_eq_zero.1 h3).resolve_left ha'

theorem eq_pointE_zero_of_forall_mem {L : Points (quadPlus 4 F)}
    (hL : ∀ γ ∈ (SpinPlus.Φ 4 F d4_three_le).roots, toStdD 4 γ 0 = 1 →
      QuotientGroup.mk' ((StatedScalars (Fin 4 ⊕ Fin 4) F).subgroupOf
          (StatedOmega (StatedQuadPlus 4 F))) (spin8OmegaEquiv F (SpinPlus.x 4 F d4_three_le γ 1)) ∈
        statedPointStabilizer (coe_quadPlus 4 F) L) :
    L = pointE F 0 := by
  obtain ⟨w, hw, hQw, rfl⟩ := exists_eq_pointMk L
  have key : ∀ j : Fin 4, j ≠ 0 → ∀ t : Bool,
      w (SpinPlus.plusIdx j (!t)) = 0 ∧ w (Sum.inr 0) = 0 := by
    intro j hj t
    obtain ⟨γ, hγ, he⟩ := exists_mem_rootsD_toStdD_eq 4 (Ne.symm hj : (0 : Fin 4) ≠ j)
      (Or.inl rfl : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1) (boolSign_eq_one_or_eq_neg_one t)
    have he' : toStdD 4 γ = Pi.single 0 (boolSign true) + Pi.single j (boolSign t) := he
    have h0 : toStdD 4 γ 0 = 1 := by
      rw [he']
      simp [Ne.symm hj]
    obtain ⟨a, ha⟩ := (mk_mem_statedPointStabilizer_iff _ w hw hQw).1 (hL γ hγ h0)
    rw [coe_spin8OmegaEquiv, spinMatrix_x_mulVec (Ne.symm hj) he'] at ha
    exact coord_eq_zero_of_smul_eq hj ha
  have hw' : w = w (Sum.inl 0) • plusVec 4 F 0 true := by
    funext k
    rcases k with m | m
    · by_cases hm : m = 0
      · subst hm
        simp [plusVec]
      · have h1 := (key m hm false).1
        simp only [Bool.not_false, SpinPlus.plusIdx] at h1
        simp [plusVec, hm, h1]
    · by_cases hm : m = 0
      · subst hm
        have h1 := (key 1 (by decide) true).2
        simp [plusVec, h1]
      · have h1 := (key m hm true).1
        simp only [Bool.not_true, SpinPlus.plusIdx] at h1
        simp [plusVec, h1]
  rw [pointE, pointMk_eq_iff]
  exact ⟨w (Sum.inl 0), hw'.symm⟩

theorem statedPointStabilizer_pointE_zero_ne_one :
    statedPointStabilizer (coe_quadPlus 4 F) (pointE F 0) ≠
      statedPointStabilizer (coe_quadPlus 4 F) (pointE F 1) := by
  intro h
  have hα : toStdD 4 (Pi.single 0 1) =
      Pi.single (0 : Fin 4) (boolSign true) + Pi.single 1 (boolSign false) := by
    funext a
    fin_cases a <;> simp [toStdD]
  have hroot : (Pi.single 0 1 : Fin 4 → ℤ) ∈ (SpinPlus.Φ 4 F d4_three_le).roots :=
    (SpinPlus.Φ 4 F d4_three_le).single_mem 0
  have h0 := mk_x_mem_stab_pointE (F := F) hroot (m := 0) (by rw [hα]; simp) 1
  rw [h, pointE, mk_mem_statedPointStabilizer_iff] at h0
  obtain ⟨a, ha⟩ := h0
  rw [coe_spin8OmegaEquiv, spinMatrix_x_mulVec (by decide) hα] at ha
  have h1 := congrFun ha (Sum.inl 0)
  simp [plusVec, SpinPlus.plusIdx, Pi.single_apply] at h1

end Stated

section Family

open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (automorphismTransport_symm_apply)

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem plusCoordinateEquiv_mk_spin8 (g : spinGroup (quadPlus 4 F)) :
    plusCoordinateEquiv 4 F (QuotientGroup.mk' ((StatedScalars (Fin 4 ⊕ Fin 4) F).subgroupOf
        (StatedOmega (StatedQuadPlus 4 F))) (spin8OmegaEquiv F g)) = spin8Equiv F g :=
  plusCoordinateEquiv_mk 4 F (by norm_num) _

theorem statedTriality_mk (g : spinGroup (quadPlus 4 F)) :
    (MulAut.congr (plusCoordinateEquiv 4 F)).symm (plusFourTriality F)
        (QuotientGroup.mk' ((StatedScalars (Fin 4 ⊕ Fin 4) F).subgroupOf
          (StatedOmega (StatedQuadPlus 4 F))) (spin8OmegaEquiv F g)) =
      QuotientGroup.mk' ((StatedScalars (Fin 4 ⊕ Fin 4) F).subgroupOf
          (StatedOmega (StatedQuadPlus 4 F)))
        (spin8OmegaEquiv F (spinGraphAut d4TrialitySym g)) := by
  rw [automorphismTransport_symm_apply, plusCoordinateEquiv_mk_spin8]
  apply (plusCoordinateEquiv 4 F).injective
  rw [MulEquiv.apply_symm_apply, plusCoordinateEquiv_mk_spin8, plusFourTriality,
    plusFourGraphAut_apply, MulEquiv.symm_apply_apply]

theorem plusFourTriality_smul_pointFamily_ne :
    plusFourTriality F • projectivePointFamily (coordinateQuadPlus 4 F) ≠
      projectivePointFamily (coordinateQuadPlus 4 F) := by
  intro h
  set τs := (MulAut.congr (plusCoordinateEquiv 4 F)).symm (plusFourTriality F) with hτs
  have hτ : plusFourTriality F = MulAut.congr (plusCoordinateEquiv 4 F) τs := by
    rw [hτs, MulEquiv.apply_symm_apply]
  rw [← plusCoordinate_pointFamily (n := 4) (K := F), hτ, ← familyTransport_automorphism] at h
  have h' : τs • statedPointFamily (coe_quadPlus 4 F) = statedPointFamily (coe_quadPlus 4 F) :=
    (familyTransport (plusCoordinateEquiv 4 F)).injective h
  have hgen : ∀ γ ∈ (SpinPlus.Φ 4 F d4_three_le).roots, toStdD 4 γ 0 = 1 → ∀ m : Fin 4,
      m = 0 ∨ m = 1 →
        τs (QuotientGroup.mk' ((StatedScalars (Fin 4 ⊕ Fin 4) F).subgroupOf
          (StatedOmega (StatedQuadPlus 4 F)))
            (spin8OmegaEquiv F (SpinPlus.x 4 F d4_three_le γ 1))) ∈
          statedPointStabilizer (coe_quadPlus 4 F) (pointE F m) := by
    intro γ hγ h0 m hm
    rw [hτs, statedTriality_mk, spinGraphAut_x d4TrialitySym hγ]
    have hρ : fundPerm d4TrialityPerm γ ∈ (SpinPlus.Φ 4 F d4_three_le).roots :=
      fundPerm_mem_spinRoots d4TrialitySym hγ
    obtain ⟨n0, n1⟩ := toStdD_triality_nonneg hγ h0
    rcases hm with rfl | rfl
    · exact mk_x_mem_stab_pointE hρ n0 1
    · exact mk_x_mem_stab_pointE hρ n1 1
  have hpre : ∀ m : Fin 4, m = 0 ∨ m = 1 →
      τs • statedPointStabilizer (coe_quadPlus 4 F) (pointE F 0) =
        statedPointStabilizer (coe_quadPlus 4 F) (pointE F m) := by
    intro m hm
    have hmem : statedPointStabilizer (coe_quadPlus 4 F) (pointE F m) ∈
        τs • statedPointFamily (coe_quadPlus 4 F) := by
      rw [h']
      exact ⟨pointE F m, rfl⟩
    obtain ⟨S, ⟨L, rfl⟩, hS⟩ := hmem
    have hL : L = pointE F 0 := by
      refine eq_pointE_zero_of_forall_mem fun γ hγ h0 => ?_
      have h1 := hgen γ hγ h0 m hm
      rw [← hS, ← MulAut.smul_def] at h1
      exact Subgroup.smul_mem_pointwise_smul_iff.1 h1
    rw [← hL]
    exact hS
  exact statedPointStabilizer_pointE_zero_ne_one
    ((hpre 0 (Or.inl rfl)).symm.trans (hpre 1 (Or.inr rfl)))

end Family

end CFSG.SeitzReduction.OmegaPilot
