module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEndField
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaDickson
public import CFSG.RankThree.PartOne.AUTSL.OmegaDickson

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Matrix
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus plusIndexEquiv
  regular_coordinateQuadPlus)
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.UnbalancedCatalog (symmetryGL symmetryGL_mem symmetryGL_mul_self
  symmetryGL_mulVec_of_charTwo symmetryIsometry symmetryAut kappa_derived_eq_conj
  matrixLinearIso_symmetryGL)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (evenOrthogonalRealization_of_regular
  unitMultiplierPairs)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (fieldAutT fieldPair)
open CFSG.RankThree.OrthogonalInvolutions (commSpace)

section Model

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

@[expose] noncomputable def plusUnitVector (hn : 1 ≤ n) : Fin (2 * n) → F :=
  (1 : F) • Pi.single (plusIndexEquiv n (.inl ⟨0, by omega⟩)) 1 +
    (1 : F) • Pi.single (plusIndexEquiv n (.inr ⟨0, by omega⟩)) 1 + 0

theorem map_plusUnitVector (hn : 1 ≤ n) : coordinateQuadPlus n F (plusUnitVector hn) = 1 := by
  rw [plusUnitVector, (isHypCoord_coordinateQuadPlus (K := F) (n := n) ⟨0, by omega⟩).map_add_smul
    1 1 rfl rfl, QuadraticMap.map_zero, mul_one, add_zero]

theorem coordinateFieldMap_plusUnitVector (hn : 1 ≤ n) (σ : F ≃+* F) :
    coordinateFieldMap (2 * n) σ (plusUnitVector hn) = plusUnitVector hn := by
  funext i
  rw [coordinateFieldMap_apply, plusUnitVector]
  simp only [one_smul, Pi.add_apply, Pi.single_apply]
  split_ifs <;> simp

theorem polar_coordinateFieldMap (σ : F ≃+* F) (x y : Fin (2 * n) → F) :
    polar (coordinateQuadPlus n F) (coordinateFieldMap (2 * n) σ x)
        (coordinateFieldMap (2 * n) σ y) =
      σ (polar (coordinateQuadPlus n F) x y) := by
  simp only [polar, ← map_add, E7Pilot.coordinateQuadPlus_fieldMap, map_sub]

theorem glFieldAut_symmetryGL (hn : 1 ≤ n) (σ : F ≃+* F) :
    glFieldAut (Fin (2 * n)) F σ (symmetryGL (coordinateQuadPlus n F) (plusUnitVector hn)) =
      symmetryGL (coordinateQuadPlus n F) (plusUnitVector hn) := by
  have hv := map_plusUnitVector (F := F) hn
  have hσv := coordinateFieldMap_plusUnitVector (F := F) hn σ
  have key : ∀ w : Fin (2 * n) → F,
      (glFieldAut (Fin (2 * n)) F σ (symmetryGL (coordinateQuadPlus n F) (plusUnitVector hn)) :
        Matrix (Fin (2 * n)) (Fin (2 * n)) F) *ᵥ w =
      (symmetryGL (coordinateQuadPlus n F) (plusUnitVector hn) :
        Matrix (Fin (2 * n)) (Fin (2 * n)) F) *ᵥ w := by
    intro w
    obtain ⟨w', rfl⟩ := (coordinateFieldMap (2 * n) σ).surjective w
    have h1 := coordinateFieldMap_matrix σ
      (symmetryGL (coordinateQuadPlus n F) (plusUnitVector hn)) w'
    rw [matrixLinearEquiv_apply, matrixLinearEquiv_apply] at h1
    have hp := polar_coordinateFieldMap (n := n) σ (plusUnitVector hn) w'
    rw [hσv] at hp
    rw [← h1, symmetryGL_mulVec_of_charTwo hv, symmetryGL_mulVec_of_charTwo hv, map_add,
      coordinateFieldMap_smul, hσv, hp]
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  have h := congrFun (key (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using h

theorem matrixIsometryInclusion_symmetry_mul_fieldPair (hn : 1 ≤ n) (σ : F ≃+* F) :
    matrixIsometryInclusion (coordinateQuadPlus n F)
        (symmetryIsometry (coordinateQuadPlus n F) (plusUnitVector hn)) *
      fieldPair (coordinateQuadPlus n F) σ (E7Pilot.coordinateQuadPlus_fieldMap n σ) =
    fieldPair (coordinateQuadPlus n F) σ (E7Pilot.coordinateQuadPlus_fieldMap n σ) *
      matrixIsometryInclusion (coordinateQuadPlus n F)
        (symmetryIsometry (coordinateQuadPlus n F) (plusUnitVector hn)) := by
  apply Subtype.ext
  apply SemidirectProduct.ext
  · change symmetryGL (coordinateQuadPlus n F) (plusUnitVector hn) *
        glFieldAut (Fin (2 * n)) F 1 1 =
      1 * glFieldAut (Fin (2 * n)) F σ (symmetryGL (coordinateQuadPlus n F) (plusUnitVector hn))
    rw [map_one, mul_one, one_mul, glFieldAut_symmetryGL]
  · change (1 : F ≃+* F) * σ = σ * 1
    rw [one_mul, mul_one]

theorem eq_matrixIsometryInclusion_mul_fieldPair
    (g : unitMultiplierPairs (coordinateQuadPlus n F)) :
    (g : similarityPairs (coordinateQuadPlus n F)) =
      matrixIsometryInclusion (coordinateQuadPlus n F)
          ⟨_, SymplecticPilot.left_mem_matrixIsometries_of_unit
            (E7Pilot.coordinateQuadPlus_fieldMap n) g⟩ *
        fieldPair (coordinateQuadPlus n F) (g : similarityPairs (coordinateQuadPlus n F)).val.right
          (E7Pilot.coordinateQuadPlus_fieldMap n _) := by
  apply Subtype.ext
  apply SemidirectProduct.ext
  · change (g : similarityPairs (coordinateQuadPlus n F)).val.left =
      (g : similarityPairs (coordinateQuadPlus n F)).val.left * glFieldAut (Fin (2 * n)) F 1 1
    rw [map_one, mul_one]
  · change (g : similarityPairs (coordinateQuadPlus n F)).val.right =
      1 * (g : similarityPairs (coordinateQuadPlus n F)).val.right
    rw [one_mul]

theorem exists_kappa_isometry_eq (hn : 4 ≤ n) (A : matrixIsometries (coordinateQuadPlus n F)) :
    ∃ x : matrixProjectiveDerived (coordinateQuadPlus n F),
      matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ A) = MulAut.conj x ∨
      matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ A) =
        MulAut.conj x * symmetryAut (coordinateQuadPlus n F) (plusUnitVector (by omega)) := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus n F (by omega)
  set v := plusUnitVector (F := F) (n := n) (by omega) with hvdef
  have hv : coordinateQuadPlus n F v = 1 := map_plusUnitVector _
  have : Invertible (coordinateQuadPlus n F v) := by rw [hv]; exact invertibleOne
  set s := symmetryGL (coordinateQuadPlus n F) v with hsdef
  have hsO : s ∈ matrixIsometries (coordinateQuadPlus n F) := symmetryGL_mem _ _
  have hs1 : (Module.finrank F (commSpace (matrixLinearIso s)) : ZMod 2) = 1 := by
    rw [hsdef, matrixLinearIso_symmetryGL, CFSG.ClassicalGroups.Orthogonal.reflect_eq_reflection,
      CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_reflection hQ, Nat.cast_one]
  rcases Nat.even_or_odd (Module.finrank F (commSpace (matrixLinearIso (A : GL (Fin (2 * n)) F))))
    with hev | hodd
  ·
    have hAd : (A : GL (Fin (2 * n)) F) ∈ matrixDerived (coordinateQuadPlus n F) :=
      (CFSG.RankThree.PartOne.AUTSL.mem_matrixDerived_iff_even hQ hT A.2).2 hev
    refine ⟨matrixProjectiveProjection _ ⟨_, hAd⟩, Or.inl ?_⟩
    rw [← kappa_derived_eq_conj]
    rfl
  ·
    have hAs : (A : GL (Fin (2 * n)) F) * s ∈ matrixDerived (coordinateQuadPlus n F) := by
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

end Model

theorem omegaPlusAutNormalFormInput_holds : OmegaPlusAutNormalFormInput := by
  intro F _ _ _ n hn
  obtain ⟨g, hg, hFc⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := F)
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus n F (by omega)
  have hE := CFSG.ComponentClassification.CatalogueBOrthogonalPointData.commutator_coordinateQuadPlus
    (K := F) (n := n) (by omega)
  obtain ⟨-, -, -, huniq, Fm, hFm, -, -, -⟩ :=
    evenOrthogonalRealization_of_regular hg hFc (by omega : 1 ≤ 2 * n) _ hQ hT hE
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus F n hn
  have hmem : ∀ α : MulAut (matrixProjectiveDerived (coordinateQuadPlus n F)),
      α ∈ matrixProjectiveImage (coordinateQuadPlus n F) := fun α => by
    rw [htop]
    exact mem_top α
  set ιt : MulAut (matrixProjectiveDerived (coordinateQuadPlus n F)) →*
      matrixProjectiveImage (coordinateQuadPlus n F) :=
    (MonoidHom.id _).codRestrict _ hmem with hιt
  have hΦκ : ∀ S : similarityPairs (coordinateQuadPlus n F),
      (Fm.comp ιt) (matrixProjectiveConjugationHom _ S) = S.val.right := fun S => hFm S
  set v := plusUnitVector (F := F) (n := n) (by omega) with hvdef
  refine ⟨Fm.comp ιt, symmetryAut (coordinateQuadPlus n F) v, fun x => ?_, fun σ => ?_, ?_, ?_,
    fun σ => ?_, fun α => ?_⟩
  · obtain ⟨y, rfl⟩ := matrixProjectiveProjection_surjective _ x
    rw [← kappa_derived_eq_conj, hΦκ]
    rfl
  · exact hΦκ _
  · rw [← _root_.sq]
    exact CFSG.ComponentClassification.UnbalancedCatalog.symmetryAut_sq _ _
  · exact hΦκ _
  · change matrixProjectiveConjugationHom _ _ * matrixProjectiveConjugationHom _ _ =
      matrixProjectiveConjugationHom _ _ * matrixProjectiveConjugationHom _ _
    rw [← map_mul, ← map_mul, matrixIsometryInclusion_symmetry_mul_fieldPair]
  · obtain ⟨S, ⟨hS, hSα⟩, -⟩ := huniq α (hmem α)
    obtain ⟨x, hx | hx⟩ := exists_kappa_isometry_eq (by omega)
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

end CFSG.SeitzReduction.OmegaPilot
