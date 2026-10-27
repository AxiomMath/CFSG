module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIUnitarySocleSteps
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailCharTwoSign
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityOrthOddCore

public noncomputable section

namespace CFSG.ComponentClassification.EvenOrthSelector

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer (mem_matrixDerived_iff)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.ComponentInitial (bilinIsometryGroup)

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem exists_eq_one [Finite K] [CharP K 2] (hd : 1 ≤ d) (hQ : Q.polarBilin.Nondegenerate) :
    ∃ v, Q v = 1 := by
  obtain ⟨w, hw⟩ :=
    LocalAnalysis.ComponentInitial.UnitaryHigher.exists_ne_zero_of_polar_nondegenerate hd hQ
  obtain ⟨c, hc⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (Q w)⁻¹
  refine ⟨c • w, ?_⟩
  rw [QuadraticMap.map_smul, smul_eq_mul, ← hc, inv_mul_cancel₀ hw]

abbrev symKappa (Q : QuadraticForm K (Fin d → K)) (v : Fin d → K) :
    derivedSymmetryCentralizer Q v →* MulAut (matrixProjectiveDerived Q) :=
  (matrixProjectiveConjugationHom Q).comp ((matrixIsometryInclusion Q).comp
    (Subgroup.inclusion (fun _ hg => hg.2.1 :
      derivedSymmetryCentralizer Q v ≤ matrixIsometries Q)))

section Regular

variable [Finite K] [CharP K 2] (hQ : Q.polarBilin.Nondegenerate)
  (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
  (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
    elementaryGroup Q)
include hQ hT hE

theorem symmetryGL_not_mem_matrixDerived {v : Fin d → K} (hv : Q v = 1) :
    symmetryGL Q v ∉ matrixDerived Q := by
  intro h
  have h1 := (mem_matrixDerived_iff Q _).mp h
  rw [matrixLinearIso_symmetryGL, hE] at h1
  obtain ⟨-, -, -, hsep⟩ :=
    LocalAnalysis.ComponentInitial.OrthogonalTail.orthogonal_geometry_char_two_reflection_separation
      hQ hT
  exact hsep v (by rw [hv]; exact one_ne_zero) h1

theorem exists_derivedSymmetryEquiv {v : Fin d → K} (hv : Q v = 1) :
    Nonempty (derivedSymmetryCentralizer Q v ≃* bilinIsometryGroup (vQuotForm Q v)) := by
  have hle : derivedSymmetryCentralizer Q v ≤ symmetryCentralizer Q v := fun _ hg => hg.2
  set φ : derivedSymmetryCentralizer Q v →* bilinIsometryGroup (vQuotForm Q v) :=
    ((symmetryRestrict hQ hv).comp (Subgroup.inclusion hle)).codRestrict _
      (fun g => symmetryRestrict_mem hQ hv _) with hφ
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨g, hg, hgy⟩ : y.val ∈ ((derivedSymmetryCentralizer Q v).subgroupOf
        (symmetryCentralizer Q v)).map (symmetryRestrict hQ hv) := by
      rw [map_derived_symmetryRestrict hQ hv hE]
      exact y.2
    exact ⟨⟨g, Subgroup.mem_subgroupOf.mp hg⟩, Subtype.ext hgy⟩
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx1 : symmetryRestrict hQ hv (Subgroup.inclusion hle x) = 1 :=
      congrArg Subtype.val hx
    rcases eq_one_or_eq_symmetryGL_of_restrict_eq_one hQ hv hx1 with h | h
    · exact Subtype.ext h
    · exfalso
      refine symmetryGL_not_mem_matrixDerived hQ hT hE hv ?_
      rw [← h]
      exact x.2.1
  exact ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩

omit [Finite K] in
theorem range_symKappa (hd : 1 ≤ d) (v : Fin d → K) :
    (symKappa Q v).range =
      inner (matrixProjectiveDerived Q) ⊓ Subgroup.centralizer {symmetryAut Q v} := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    have hgD : (g : GL (Fin d) K) ∈ matrixDerived Q := g.2.1
    refine ⟨⟨matrixProjectiveProjection Q ⟨g, hgD⟩, (kappa_derived_eq_conj ⟨_, hgD⟩).symm⟩, ?_⟩
    have hc : Commute (Subgroup.inclusion (fun _ hg => hg.2.1 :
        derivedSymmetryCentralizer Q v ≤ matrixIsometries Q) g) (symmetryIsometry Q v) :=
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2.2.2)
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((hc.map (matrixIsometryInclusion Q)).map (matrixProjectiveConjugationHom Q)).eq
  · rintro y ⟨⟨x, rfl⟩, hy⟩
    obtain ⟨g, rfl⟩ := matrixProjectiveProjection_surjective Q x
    have hκ := kappa_derived_eq_conj g
    have hcomm : Subgroup.inclusion (matrixDerived_le_isometries Q) g * symmetryIsometry Q v =
        symmetryIsometry Q v * Subgroup.inclusion (matrixDerived_le_isometries Q) g := by
      apply kappa_inclusion_injective hQ hT hE hd
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp hy
      rw [← hκ] at h1
      simp only [MonoidHom.comp_apply, map_mul]
      exact h1
    refine ⟨⟨g, g.2, (matrixDerived_le_isometries Q) g.2,
      Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hcomm)⟩, ?_⟩
    exact hκ

theorem symmetry_component {f n : ℕ} (hK : Nat.card K = 2 ^ f) (hdn : d = 2 * n) (hn : 4 ≤ n)
    {v : Fin d → K} (hv : Q v = 1) {X : Subgroup (MulAut (matrixProjectiveDerived Q))}
    (hX : CFSG.Assembly.IsComponentOf X
      (inner (matrixProjectiveDerived Q) ⊓ Subgroup.centralizer {symmetryAut Q v})) :
    IsSimpleGroup X ∧ Nonempty (X ≃* StatedSp (n - 1) K) := by
  have hd : 1 ≤ d := by omega
  rw [← range_symKappa hQ hT hE hd v] at hX
  obtain ⟨eB⟩ := exists_derivedSymmetryEquiv hQ hT hE hv
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hv
    exact zero_ne_one hv
  have hdim : Module.finrank K (vQuot Q v) = 2 * (n - 1) := by
    have := finrank_vQuot hQ hv
    omega
  have hinj : Function.Injective (symKappa Q v) :=
    (kappa_inclusion_injective hQ hT hE hd).comp (Subgroup.inclusion_injective _)
  rcases OutcomeLocal.symplectic_component_dichotomy hinj hX hK (by omega : 1 ≤ n - 1)
      (by omega) (vQuotForm Q v) (vQuotForm_isAlt Q v) (vQuotForm_nondegenerate hQ hv0) hdim
      (eB.trans (bilinIsometryGroupEquiv _)) with ⟨-, -, hs, -, hSp⟩ | ⟨-, hr2, -⟩
  · exact ⟨hs, hSp⟩
  · omega

end Regular

end CFSG.ComponentClassification.EvenOrthSelector
