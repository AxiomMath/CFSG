module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotFiveFamily
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEndFieldAut

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Matrix
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus StatedProj StatedScalars)
open CFSG.ClassicalGroups.Orthogonal (toLinEquiv toLinEquiv_apply)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit (flag Xstar mem_flag_top mem_Xstar)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus plusIndexEquiv
  regular_coordinateQuadPlus)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
  (statedProjectiveSubspaceStabilizer statedDerivedSubspaceStabilizer
    mem_statedProjectiveSubspaceStabilizer_mk mem_statedDerivedSubspaceStabilizer)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit (plusCX plusCXstar
  plusCoordinateEquiv)
open CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit (conjugacyFamily
  conjugacyFamily_covariance conj_conjugacyFamily)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (fieldAutT fieldPair fieldAutT_mk
  matrixDerivedConjugation_fieldPair_val)
open scoped Pointwise

section Field

variable {F : Type} [Field F] [CharP F 2] {n : ℕ}

@[expose] noncomputable def statedFieldConj (σ : F ≃+* F) (A : StatedOmega (StatedQuadPlus n F)) :
    StatedOmega (StatedQuadPlus n F) :=
  (statedDerivedPlusEquiv F n).symm (matrixDerivedConjugation (coordinateQuadPlus n F)
    (fieldPair (coordinateQuadPlus n F) σ (E7Pilot.coordinateQuadPlus_fieldMap n σ))
    (statedDerivedPlusEquiv F n A))

omit [CharP F 2] in
theorem statedFieldConj_entry (σ : F ≃+* F) (A : StatedOmega (StatedQuadPlus n F))
    (i j : Fin n ⊕ Fin n) :
    ((statedFieldConj σ A : StatedOmega (StatedQuadPlus n F)) : GL (Fin n ⊕ Fin n) F).val i j =
      σ ((A : GL (Fin n ⊕ Fin n) F).val i j) := by
  rw [statedFieldConj, statedDerivedPlusEquiv_symm_entry, matrixDerivedConjugation_fieldPair_val]
  have h := statedDerivedPlusEquiv_symm_entry F n (statedDerivedPlusEquiv F n A) i j
  rw [MulEquiv.symm_apply_apply] at h
  rw [h]
  rfl

omit [CharP F 2] in
theorem toLinEquiv_statedFieldConj (σ : F ≃+* F) (A : StatedOmega (StatedQuadPlus n F))
    (v : Fin n ⊕ Fin n → F) :
    toLinEquiv (Fin n ⊕ Fin n) F (statedFieldConj σ A : GL (Fin n ⊕ Fin n) F)
        (fun i => σ (v i)) =
      fun i => σ (toLinEquiv (Fin n ⊕ Fin n) F (A : GL (Fin n ⊕ Fin n) F) v i) := by
  funext i
  simp only [toLinEquiv_apply, Matrix.mulVec, dotProduct, map_sum, map_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [statedFieldConj_entry]

theorem fieldAutHom_statedOmegaPlusEquiv (hn : 1 ≤ n) (σ : F ≃+* F)
    (A : StatedOmega (StatedQuadPlus n F)) :
    fieldAutHom F n σ (statedOmegaPlusEquiv F n hn A) =
      statedOmegaPlusEquiv F n hn (statedFieldConj σ A) := by
  change fieldAutT (coordinateQuadPlus n F) σ (E7Pilot.coordinateQuadPlus_fieldMap n σ)
      (matrixProjectiveProjection _ (statedDerivedPlusEquiv F n A)) =
    matrixProjectiveProjection _ (statedDerivedPlusEquiv F n (statedFieldConj σ A))
  rw [fieldAutT_mk, statedFieldConj, MulEquiv.apply_symm_apply]

omit [CharP F 2] in
theorem statedFieldConj_mem_stabilizer (σ : F ≃+* F) {W : Submodule F (Fin n ⊕ Fin n → F)}
    (hW : ∀ v ∈ W, (fun i => σ (v i)) ∈ W) (hW' : ∀ v ∈ W, (fun i => σ.symm (v i)) ∈ W)
    {A : StatedOmega (StatedQuadPlus n F)}
    (hA : A ∈ statedDerivedSubspaceStabilizer (StatedQuadPlus n F) W) :
    statedFieldConj σ A ∈ statedDerivedSubspaceStabilizer (StatedQuadPlus n F) W := by
  rw [mem_statedDerivedSubspaceStabilizer] at hA ⊢
  have hAW : ∀ w ∈ W, toLinEquiv (Fin n ⊕ Fin n) F (A : GL (Fin n ⊕ Fin n) F) w ∈ W := by
    intro w hw
    rw [← hA]
    exact ⟨w, hw, rfl⟩
  have hle : W.map (toLinEquiv (Fin n ⊕ Fin n) F
      (statedFieldConj σ A : GL (Fin n ⊕ Fin n) F)).toLinearMap ≤ W := by
    rintro _ ⟨v, hv, rfl⟩
    have hv' : v = fun i => σ ((fun j => σ.symm (v j)) i) := by
      funext i
      simp
    change toLinEquiv (Fin n ⊕ Fin n) F (statedFieldConj σ A : GL (Fin n ⊕ Fin n) F) v ∈ W
    rw [hv', toLinEquiv_statedFieldConj]
    exact hW _ (hAW _ (hW' v hv))
  exact Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq _ _)

end Field

section Families

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem map_map_statedStabilizer_fieldAutHom (hn : 1 ≤ n) (σ : F ≃+* F)
    {W : Submodule F (Fin n ⊕ Fin n → F)}
    (hW : ∀ v ∈ W, (fun i => σ (v i)) ∈ W) (hW' : ∀ v ∈ W, (fun i => σ.symm (v i)) ∈ W) :
    ((statedProjectiveSubspaceStabilizer (StatedQuadPlus n F) W).map
        (plusCoordinateEquiv n F).toMonoidHom).map (fieldAutHom F n σ).toMonoidHom =
      (statedProjectiveSubspaceStabilizer (StatedQuadPlus n F) W).map
        (plusCoordinateEquiv n F).toMonoidHom := by
  set H := statedProjectiveSubspaceStabilizer (StatedQuadPlus n F) W with hH
  have hle : (H.map (plusCoordinateEquiv n F).toMonoidHom).map (fieldAutHom F n σ).toMonoidHom ≤
      H.map (plusCoordinateEquiv n F).toMonoidHom := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective _ y
    have hA : A ∈ statedDerivedSubspaceStabilizer (StatedQuadPlus n F) W :=
      (mem_statedProjectiveSubspaceStabilizer_mk _ W A).1 hy
    refine ⟨QuotientGroup.mk' _ (statedFieldConj σ A),
      (mem_statedProjectiveSubspaceStabilizer_mk _ W _).2
        (statedFieldConj_mem_stabilizer σ hW hW' hA), ?_⟩
    change plusCoordinateEquiv n F (QuotientGroup.mk' _ (statedFieldConj σ A)) =
      fieldAutHom F n σ (plusCoordinateEquiv n F (QuotientGroup.mk' _ A))
    rw [plusCoordinateEquiv_mk n F hn, plusCoordinateEquiv_mk n F hn,
      fieldAutHom_statedOmegaPlusEquiv]
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (f := (fieldAutHom F n σ).toMonoidHom)
    (MulEquiv.injective (fieldAutHom F n σ))]

theorem fieldAutHom_smul_plusCX (hn : 1 ≤ n) (σ : F ≃+* F) :
    fieldAutHom F n σ • plusCX n F = plusCX n F := by
  rw [plusCX, conjugacyFamily_covariance, map_map_statedStabilizer_fieldAutHom hn σ]
  · intro v hv
    rw [mem_flag_top] at hv ⊢
    intro i
    rw [hv i, map_zero]
  · intro v hv
    rw [mem_flag_top] at hv ⊢
    intro i
    rw [hv i, map_zero]

theorem fieldAutHom_smul_plusCXstar (hn : 1 ≤ n) (σ : F ≃+* F) :
    fieldAutHom F n σ • plusCXstar n F (by omega) = plusCXstar n F (by omega) := by
  rw [plusCXstar, conjugacyFamily_covariance, map_map_statedStabilizer_fieldAutHom hn σ]
  · intro v hv
    rw [mem_Xstar] at hv ⊢
    refine ⟨by rw [hv.1, map_zero], fun k hk => ?_⟩
    rw [hv.2 k hk, map_zero]
  · intro v hv
    rw [mem_Xstar] at hv ⊢
    refine ⟨by rw [hv.1, map_zero], fun k hk => ?_⟩
    rw [hv.2 k hk, map_zero]

end Families

section NormalForm

open CFSG.ComponentClassification.UnbalancedCatalog (symmetryGL symmetryGL_mem symmetryGL_mul_self
  symmetryIsometry symmetryAut kappa_derived_eq_conj matrixLinearIso_symmetryGL)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (evenOrthogonalRealization_of_regular)
open CFSG.RankThree.OrthogonalInvolutions (commSpace)
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem exists_kappa_isometry_eq_of_unit (hn : 4 ≤ n) {v : Fin (2 * n) → F}
    (hv : coordinateQuadPlus n F v = 1) (A : matrixIsometries (coordinateQuadPlus n F)) :
    ∃ x : matrixProjectiveDerived (coordinateQuadPlus n F),
      matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ A) = MulAut.conj x ∨
      matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ A) =
        MulAut.conj x * symmetryAut (coordinateQuadPlus n F) v := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus n F (by omega)
  have : Invertible (coordinateQuadPlus n F v) := by rw [hv]; exact invertibleOne
  set s := symmetryGL (coordinateQuadPlus n F) v with hsdef
  have hsO : s ∈ matrixIsometries (coordinateQuadPlus n F) := symmetryGL_mem _ _
  have hs1 : (Module.finrank F (commSpace (matrixLinearIso s)) : ZMod 2) = 1 := by
    rw [hsdef, matrixLinearIso_symmetryGL, CFSG.ClassicalGroups.Orthogonal.reflect_eq_reflection,
      CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_reflection hQ, Nat.cast_one]
  rcases Nat.even_or_odd (Module.finrank F (commSpace (matrixLinearIso (A : GL (Fin (2 * n)) F))))
    with hev | hodd
  · have hAd : (A : GL (Fin (2 * n)) F) ∈ matrixDerived (coordinateQuadPlus n F) :=
      (CFSG.RankThree.PartOne.AUTSL.mem_matrixDerived_iff_even hQ hT A.2).2 hev
    refine ⟨matrixProjectiveProjection _ ⟨_, hAd⟩, Or.inl ?_⟩
    rw [← kappa_derived_eq_conj]
    rfl
  · have hAs : (A : GL (Fin (2 * n)) F) * s ∈ matrixDerived (coordinateQuadPlus n F) := by
      refine (CFSG.RankThree.PartOne.AUTSL.mem_matrixDerived_iff_even hQ hT
        (mul_mem A.2 hsO)).2 ?_
      rw [← ZMod.natCast_eq_zero_iff_even, map_mul,
        CFSG.RankThree.OrthogonalInvolutions.natCast_finrank_commSpace_mul
          (g := matrixLinearIso (A : GL (Fin (2 * n)) F)) (h := matrixLinearIso s) hQ A.2 hsO, hs1,
        ZMod.natCast_eq_one_iff_odd.2 hodd]
      decide
    refine ⟨matrixProjectiveProjection _ ⟨_, hAs⟩, Or.inr ?_⟩
    rw [← kappa_derived_eq_conj, symmetryAut, ← map_mul]
    congr 1
    apply Subtype.ext
    apply SemidirectProduct.ext
    · change (A : GL (Fin (2 * n)) F) =
        (A : GL (Fin (2 * n)) F) * s * glFieldAut (Fin (2 * n)) F 1 s
      rw [map_one, MulAut.one_apply, mul_assoc, symmetryGL_mul_self, mul_one]
    · rfl

theorem mem_image_normalForm (hn : 4 ≤ n) {v : Fin (2 * n) → F}
    (hv : coordinateQuadPlus n F v = 1)
    {α : MulAut (matrixProjectiveDerived (coordinateQuadPlus n F))}
    (hα : α ∈ matrixProjectiveImage (coordinateQuadPlus n F)) :
    ∃ x, ∃ c : F ≃+* F, α = MulAut.conj x * fieldAutHom F n c ∨
      α = MulAut.conj x * symmetryAut (coordinateQuadPlus n F) v * fieldAutHom F n c := by
  obtain ⟨g, hg, hFc⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := F)
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus n F (by omega)
  have hE := CFSG.ComponentClassification.CatalogueBOrthogonalPointData.commutator_coordinateQuadPlus
    (K := F) (n := n) (by omega)
  obtain ⟨-, -, -, huniq, -, -, -, -, -⟩ :=
    evenOrthogonalRealization_of_regular hg hFc (by omega : 1 ≤ 2 * n) _ hQ hT hE
  obtain ⟨S, ⟨hS, hSα⟩, -⟩ := huniq α hα
  obtain ⟨x, hx | hx⟩ := exists_kappa_isometry_eq_of_unit hn hv
    ⟨_, SymplecticPilot.left_mem_matrixIsometries_of_unit
      (E7Pilot.coordinateQuadPlus_fieldMap n) ⟨S, hS⟩⟩
  · refine ⟨x, S.val.right, Or.inl ?_⟩
    have h1 := congrArg (matrixProjectiveConjugationHom (coordinateQuadPlus n F))
      (eq_matrixIsometryInclusion_mul_fieldPair (F := F) (n := n) ⟨S, hS⟩)
    rw [map_mul, hx] at h1
    rw [← hSα]
    exact h1
  · refine ⟨x, S.val.right, Or.inr ?_⟩
    have h1 := congrArg (matrixProjectiveConjugationHom (coordinateQuadPlus n F))
      (eq_matrixIsometryInclusion_mul_fieldPair (F := F) (n := n) ⟨S, hS⟩)
    rw [map_mul, hx] at h1
    rw [← hSα]
    exact h1

end NormalForm

end CFSG.SeitzReduction.OmegaPilot
