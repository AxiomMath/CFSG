module

public import CFSG.ClassicalGroups.Orthogonal.Derived
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentClassification.CentralExtensions
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingSymmetric

public section

namespace CFSG.ComponentClassification.CatalogueBOrthogonal

noncomputable section

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem scalarIntersection_le_center (H : Subgroup (V ≃ₗ[K] V)) :
    (scalars K V).subgroupOf H ≤ Subgroup.center H := by
  intro g hg
  apply Subgroup.mem_center_iff.mpr
  intro x
  exact Subtype.ext (commute_of_mem_scalars (Subgroup.mem_subgroupOf.mp hg) x).symm

theorem elementary_quasisimple [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : (polarBilin Q).Nondegenerate)
    {T : Submodule K V} (hT : 3 ≤ Module.finrank K T)
    (hTQ : ∀ x ∈ T, Q x = 0) : CFSG.IsQuasisimple (elementaryGroup Q) := by
  let : Group.IsPerfect (elementaryGroup Q) :=
    ⟨commutator_elementaryGroup_eq_top' hQ hT hTQ⟩
  let : IsSimpleGroup (ProjElementary Q) := isSimpleGroup_projElementary hQ hT hTQ
  have hprojective : CFSG.Open.IsQuasisimple (ProjElementary Q) :=
    Quasisimple.simple_of_perfect (ProjElementary Q)
  exact CatalogueBAlternating.quasisimple_iff_native.mpr
    (CentralExtensions.quasisimple_of_surjective hprojective
      (QuotientGroup.mk' ((scalars K V).subgroupOf (elementaryGroup Q)))
      (QuotientGroup.mk'_surjective _) (by
        simpa only [QuotientGroup.ker_mk'] using
          scalarIntersection_le_center (elementaryGroup Q)))

theorem derived_map_eq_elementary [FiniteDimensional K V]
    (Q : QuadraticForm K V) (h2 : (2 : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate)
    {T : Submodule K V} (hT : 3 ≤ Module.finrank K T)
    (hTQ : ∀ x ∈ T, Q x = 0) :
    (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)).map
      (TauCeti.QuadraticMap.orthogonalGroup Q).subtype = elementaryGroup Q := by
  rw [Subgroup.map_subtype_commutator]
  obtain ⟨P₁, P₂, P₃, h₁₂, h₁₃, h₂₃⟩ := exists_three_hypPairs hQ hT hTQ
  exact commutator_orthogonalGroup_eq_elementaryGroup_of_two_ne_zero
    h2 hQ h₁₂ h₁₃ h₂₃

@[expose] def derivedEquivElementary [FiniteDimensional K V]
    (Q : QuadraticForm K V) (h2 : (2 : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate)
    {T : Submodule K V} (hT : 3 ≤ Module.finrank K T)
    (hTQ : ∀ x ∈ T, Q x = 0) :
    commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≃* elementaryGroup Q :=
  ((commutator (TauCeti.QuadraticMap.orthogonalGroup Q)).equivMapOfInjective
    (TauCeti.QuadraticMap.orthogonalGroup Q).subtype
    (TauCeti.QuadraticMap.orthogonalGroup Q).subtype_injective).trans
      (MulEquiv.subgroupCongr (derived_map_eq_elementary Q h2 hQ hT hTQ))

theorem derivedEquivElementary_val [FiniteDimensional K V]
    (Q : QuadraticForm K V) (h2 : (2 : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate)
    {T : Submodule K V} (hT : 3 ≤ Module.finrank K T)
    (hTQ : ∀ x ∈ T, Q x = 0)
    (g : commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) :
    (derivedEquivElementary Q h2 hQ hT hTQ g : V ≃ₗ[K] V) = g.val.val := by
  rfl

theorem derived_quasisimple [FiniteDimensional K V]
    (Q : QuadraticForm K V) (h2 : (2 : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate)
    {T : Submodule K V} (hT : 3 ≤ Module.finrank K T)
    (hTQ : ∀ x ∈ T, Q x = 0) :
    CFSG.IsQuasisimple (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) :=
  CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv (derivedEquivElementary Q h2 hQ hT hTQ)
      (CatalogueBAlternating.quasisimple_iff_native.mp (elementary_quasisimple Q hQ hT hTQ)))

end

end CFSG.ComponentClassification.CatalogueBOrthogonal
