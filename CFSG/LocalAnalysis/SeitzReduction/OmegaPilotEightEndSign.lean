module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightEndBasic
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusFourMain
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverHR8Graph

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus
  coordinateQuadMinus projectivePointFamily projectivePointFamilyAut
  mem_projectivePointFamilyAut_iff projective_inner_le_pointFamilyAut)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit (plusCX plusCXstar
  coordinate_plus_pointFamily_orbit_subset)
open CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit (conj_conjugacyFamily)
open CFSG.ComponentClassification.UnbalancedCatalog (symmetryAut symmetryIsometry)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (fieldAutT fieldPair)
open CFSG.SeitzReduction.TwistedE6Pilot (coordinateQuadMinus_fieldMap_of_fixed)
open scoped Pointwise

section Triple

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem symmetryAut_lastPlaneVec_smul_plusCX :
    symmetryAut (coordinateQuadPlus 4 F) (lastPlaneVec 3) • plusCX 4 F =
        plusCXstar 4 F (by norm_num) ∧
      symmetryAut (coordinateQuadPlus 4 F) (lastPlaneVec 3) • plusCXstar 4 F (by norm_num) =
        plusCX 4 F := by
  have hγim : plusFlipAut 4 F (by norm_num) ∈ matrixProjectiveImage (coordinateQuadPlus 4 F) :=
    plusFlipAut_mem_image le_rfl
  have hv : coordinateQuadPlus 4 F (lastPlaneVec 3) = 1 := coordinateQuadPlus_lastPlaneVec
  obtain ⟨x, c, h | h⟩ := mem_image_normalForm le_rfl hv hγim
  · exfalso
    have h1 : plusFlipAut 4 F (by norm_num) • plusCX 4 F = plusCX 4 F := by
      rw [h, mul_smul, fieldAutHom_smul_plusCX (by norm_num), plusCX, conj_conjugacyFamily]
    exact plusCX_ne_plusCXstar 4 F (by norm_num) (h1.symm.trans (plusFlipAut_smul_plusCX 4 F _))
  · have hκ : symmetryAut (coordinateQuadPlus 4 F) (lastPlaneVec 3) =
        MulAut.conj x⁻¹ * plusFlipAut 4 F (by norm_num) * fieldAutHom F 4 c⁻¹ := by
      rw [map_inv, map_inv, h]
      group
    constructor
    · rw [hκ, mul_smul, mul_smul, fieldAutHom_smul_plusCX (by norm_num), plusFlipAut_smul_plusCX,
        plusCXstar, conj_conjugacyFamily]
    · rw [hκ, mul_smul, mul_smul, fieldAutHom_smul_plusCXstar (by norm_num),
        plusFlipAut_smul_plusCXstar, plusCX, conj_conjugacyFamily]

theorem smul_plusCX_of_mem_image {δ : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F))}
    (hδ : δ ∈ matrixProjectiveImage (coordinateQuadPlus 4 F)) :
    (δ • plusCX 4 F = plusCX 4 F ∧
        δ • plusCXstar 4 F (by norm_num) = plusCXstar 4 F (by norm_num)) ∨
      (δ • plusCX 4 F = plusCXstar 4 F (by norm_num) ∧
        δ • plusCXstar 4 F (by norm_num) = plusCX 4 F) := by
  obtain ⟨hγX, hγX'⟩ := symmetryAut_lastPlaneVec_smul_plusCX (F := F)
  have hv : coordinateQuadPlus 4 F (lastPlaneVec 3) = 1 := coordinateQuadPlus_lastPlaneVec
  obtain ⟨x, c, rfl | rfl⟩ := mem_image_normalForm le_rfl hv hδ
  · left
    simp only [mul_smul]
    rw [fieldAutHom_smul_plusCX (by norm_num), fieldAutHom_smul_plusCXstar (by norm_num)]
    exact ⟨by rw [plusCX, conj_conjugacyFamily], by rw [plusCXstar, conj_conjugacyFamily]⟩
  · right
    simp only [mul_smul]
    rw [fieldAutHom_smul_plusCX (by norm_num), fieldAutHom_smul_plusCXstar (by norm_num), hγX,
      hγX']
    exact ⟨by rw [plusCXstar, conj_conjugacyFamily], by rw [plusCX, conj_conjugacyFamily]⟩

variable (F) in
abbrev plusFourTripleSet : Set (Set (Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 F)))) :=
  {projectivePointFamily (coordinateQuadPlus 4 F), plusCX 4 F, plusCXstar 4 F (by norm_num)}

theorem smul_mem_plusFourTripleSet (δ : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F)))
    {Y : Set (Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 F)))}
    (hY : Y ∈ plusFourTripleSet F) : δ • Y ∈ plusFourTripleSet F := by
  have hO := coordinate_plus_pointFamily_orbit_subset (n := 4) (K := F) rfl
  by_cases hall : ∀ ε : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F)),
      ε • projectivePointFamily (coordinateQuadPlus 4 F) =
        projectivePointFamily (coordinateQuadPlus 4 F)
  · have hδ : δ ∈ matrixProjectiveImage (coordinateQuadPlus 4 F) :=
      (mem_image_iff_smul_pointFamily le_rfl δ).2 (hall δ)
    rcases hY with rfl | rfl | rfl
    · exact Or.inl (hall δ)
    · rcases smul_plusCX_of_mem_image hδ with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h1)
    · rcases smul_plusCX_of_mem_image hδ with ⟨-, h1⟩ | ⟨-, h1⟩
      · exact Or.inr (Or.inr h1)
      · exact Or.inr (Or.inl h1)
  · push Not at hall
    obtain ⟨ε, hε⟩ := hall
    have hγX := plusFlipAut_smul_plusCX 4 F (by norm_num)
    have hγX' := plusFlipAut_smul_plusCXstar 4 F (by norm_num)
    have hεO := hO ⟨ε, rfl⟩
    have hCX : plusCX 4 F ∈
          MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F)))
            (projectivePointFamily (coordinateQuadPlus 4 F)) ∧
        plusCXstar 4 F (by norm_num) ∈
          MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F)))
            (projectivePointFamily (coordinateQuadPlus 4 F)) := by
      rcases hεO with h | h | h
      · exact absurd h hε
      · have h' : ε • projectivePointFamily (coordinateQuadPlus 4 F) = plusCX 4 F := h
        refine ⟨⟨ε, h'⟩, ⟨plusFlipAut 4 F (by norm_num) * ε, ?_⟩⟩
        change (plusFlipAut 4 F (by norm_num) * ε) • projectivePointFamily (coordinateQuadPlus 4 F) =
          plusCXstar 4 F (by norm_num)
        rw [mul_smul, h', hγX]
      · have h' : ε • projectivePointFamily (coordinateQuadPlus 4 F) =
            plusCXstar 4 F (by norm_num) := h
        refine ⟨⟨plusFlipAut 4 F (by norm_num) * ε, ?_⟩, ⟨ε, h'⟩⟩
        change (plusFlipAut 4 F (by norm_num) * ε) • projectivePointFamily (coordinateQuadPlus 4 F) =
          plusCX 4 F
        rw [mul_smul, h', hγX']
    have hYO : Y ∈ MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F)))
          (projectivePointFamily (coordinateQuadPlus 4 F)) := by
      rcases hY with rfl | rfl | rfl
      · exact MulAction.mem_orbit_self _
      · exact hCX.1
      · exact hCX.2
    obtain ⟨ε', rfl⟩ := hYO
    exact hO ⟨δ * ε', mul_smul δ ε' _⟩

variable (F) in
@[expose] def plusFourTripleSub :
    SubMulAction (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F)))
      (Set (Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 F)))) where
  carrier := plusFourTripleSet F
  smul_mem' δ _ hY := smul_mem_plusFourTripleSet δ hY

instance finite_plusFourTripleSub : Finite (plusFourTripleSub F) :=
  Set.Finite.to_subtype (s := plusFourTripleSet F)
    (((Set.finite_singleton _).insert _).insert _)

theorem exists_index_two_of_swap
    {g₀ : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F))}
    (hg₀F : g₀ • projectivePointFamily (coordinateQuadPlus 4 F) =
      projectivePointFamily (coordinateQuadPlus 4 F))
    (hg₀X : g₀ • plusCX 4 F = plusCXstar 4 F (by norm_num))
    (hg₀X' : g₀ • plusCXstar 4 F (by norm_num) = plusCX 4 F) :
    ∃ E : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F))),
      E.index = 2 ∧ (∀ x, MulAut.conj x ∈ E) ∧ g₀ ∉ E := by
  classical
  have : Fintype (plusFourTripleSub F) := Fintype.ofFinite _
  set χ : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F)) →* ℤˣ :=
    Equiv.Perm.sign.comp (MulAction.toPermHom _ (plusFourTripleSub F)) with hχ
  have hXX : plusCX 4 F ≠ plusCXstar 4 F (by norm_num) := plusCX_ne_plusCXstar 4 F (by norm_num)
  have hFX : projectivePointFamily (coordinateQuadPlus 4 F) ≠ plusCX 4 F := fun h =>
    hXX (by rw [← hg₀X, ← h, hg₀F, h])
  have hFX' : projectivePointFamily (coordinateQuadPlus 4 F) ≠ plusCXstar 4 F (by norm_num) :=
    fun h => hXX (by rw [← hg₀X', ← h, hg₀F, h])
  have hInn : ∀ x, χ (MulAut.conj x) = 1 := by
    intro x
    have h1 : MulAction.toPermHom _ (plusFourTripleSub F) (MulAut.conj x) = 1 := by
      apply Equiv.ext
      rintro ⟨Y, hY⟩
      apply Subtype.ext
      change MulAut.conj x • Y = Y
      rcases hY with rfl | rfl | rfl
      · exact (mem_projectivePointFamilyAut_iff _ _).1
          (projective_inner_le_pointFamilyAut _ ⟨x, rfl⟩)
      · rw [plusCX, conj_conjugacyFamily]
      · rw [plusCXstar, conj_conjugacyFamily]
    rw [hχ, MonoidHom.comp_apply, h1, map_one]
  set a : plusFourTripleSub F := ⟨plusCX 4 F, Or.inr (Or.inl rfl)⟩ with ha
  set b : plusFourTripleSub F := ⟨plusCXstar 4 F (by norm_num), Or.inr (Or.inr rfl)⟩ with hb
  have hab : a ≠ b := fun h => hXX (congrArg Subtype.val h)
  have hg : χ g₀ = -1 := by
    have h1 : MulAction.toPermHom _ (plusFourTripleSub F) g₀ = Equiv.swap a b := by
      apply Equiv.ext
      rintro ⟨Y, hY⟩
      rcases hY with rfl | rfl | rfl
      · rw [Equiv.swap_apply_of_ne_of_ne (fun h => hFX (congrArg Subtype.val h))
          (fun h => hFX' (congrArg Subtype.val h))]
        apply Subtype.ext
        exact hg₀F
      · change _ = Equiv.swap a b a
        rw [Equiv.swap_apply_left]
        apply Subtype.ext
        exact hg₀X
      · change _ = Equiv.swap a b b
        rw [Equiv.swap_apply_right]
        apply Subtype.ext
        exact hg₀X'
    rw [hχ, MonoidHom.comp_apply, h1, Equiv.Perm.sign_swap hab]
  refine ⟨χ.ker, ?_, fun x => hInn x, fun h => ?_⟩
  · rw [Subgroup.index_eq_two_iff]
    refine ⟨g₀, fun y => ?_⟩
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, map_mul, hg]
    rcases Int.units_eq_one_or (χ y) with h | h <;> rw [h] <;> decide
  · rw [MonoidHom.mem_ker, hg] at h
    exact absurd h (by decide)

end Triple

theorem omegaMinusFourSignInput_holds : OmegaMinusFourSignInput := by
  intro F _ _ _ β γ σ hσ hβ hγ hirr
  obtain ⟨α, hα, hσα, hβ0⟩ := exists_root_frob_of_irreducible hσ hβ hγ hirr
  have hαα := root_ne_other_of_ne_zero (α := α) hβ0
  have hB := congr_minusPlusSim_fieldAutT (r := 3) (by omega) hα hαα hσα hβ hγ
  generalize minusPlusSim (r := 3) (by omega) hα hαα = B at hB
  obtain ⟨hX, hX'⟩ := symmetryAut_lastPlaneVec_smul_plusCX (F := F)
  set g₀ := symmetryAut (coordinateQuadPlus 4 F) (lastPlaneVec 3) * fieldAutHom F 4 σ with hg₀
  have hg₀im : g₀ ∈ matrixProjectiveImage (coordinateQuadPlus 4 F) :=
    mul_mem ⟨_, rfl⟩ ⟨_, rfl⟩
  have hg₀F := (mem_image_iff_smul_pointFamily le_rfl g₀).1 hg₀im
  have hg₀X : g₀ • plusCX 4 F = plusCXstar 4 F (by norm_num) := by
    rw [hg₀, mul_smul, fieldAutHom_smul_plusCX (by norm_num), hX]
  have hg₀X' : g₀ • plusCXstar 4 F (by norm_num) = plusCX 4 F := by
    rw [hg₀, mul_smul, fieldAutHom_smul_plusCXstar (by norm_num), hX']
  obtain ⟨E, hE2, hEInn, hEg⟩ := exists_index_two_of_swap hg₀F hg₀X hg₀X'
  refine ⟨E.comap (MulAut.congr B).toMonoidHom, ?_, fun x => ?_, ?_⟩
  · rw [Subgroup.index_comap_of_surjective _ (MulAut.congr B).surjective, hE2]
  · refine Subgroup.mem_comap.2 ?_
    change MulAut.congr B (MulAut.conj x) ∈ E
    rw [omegaMinus_mulAut_congr_conj B x]
    exact hEInn (B x)
  · intro hmem
    have h1 := Subgroup.mem_comap.1 hmem
    change MulAut.congr B _ ∈ E at h1
    rw [hB] at h1
    exact hEg h1

theorem omegaMinusFourEndInput_holds : OmegaMinusFourEndInput :=
  omegaMinusFourEndInput_of_sign omegaMinusFourSignInput_holds

end CFSG.SeitzReduction.OmegaPilot
