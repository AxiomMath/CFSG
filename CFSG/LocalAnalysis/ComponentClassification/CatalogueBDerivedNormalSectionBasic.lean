module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.GroupAction.ConjAct

public section

namespace CFSG.ComponentClassification.CatalogueBDerivedNormalSection

universe u v

variable {E : Type u} [Group E]

@[expose] def derivedNormalSubgroup (N : Subgroup E) : Subgroup E :=
  (commutator N).map N.subtype

theorem derivedNormalSubgroup_eq (N : Subgroup E) :
    derivedNormalSubgroup N = ⁅N, N⁆ :=
  N.map_subtype_commutator

theorem derivedNormalSubgroup_le (N : Subgroup E) :
    derivedNormalSubgroup N ≤ N := by
  rw [derivedNormalSubgroup_eq]
  exact N.commutator_le_self

instance derivedNormalSubgroupNormal (N : Subgroup E) [N.Normal] :
    (derivedNormalSubgroup N).Normal := by
  unfold derivedNormalSubgroup
  infer_instance

@[expose] def sectionDenominator (N Z : Subgroup E) :
    Subgroup (derivedNormalSubgroup N) :=
  Z.subgroupOf (derivedNormalSubgroup N)

theorem mem_sectionDenominator_iff (N Z : Subgroup E)
    (h : derivedNormalSubgroup N) :
    h ∈ sectionDenominator N Z ↔ (h : E) ∈ Z :=
  Iff.rfl

instance sectionDenominatorNormal (N Z : Subgroup E) [Z.Normal] :
    (sectionDenominator N Z).Normal := by
  unfold sectionDenominator
  infer_instance

theorem sectionDenominator_map (N Z : Subgroup E) (hZ : Z ≤ derivedNormalSubgroup N) :
    (sectionDenominator N Z).map (derivedNormalSubgroup N).subtype = Z := by
  ext z
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact hh
  · intro hz
    exact ⟨⟨z, hZ hz⟩, hz, rfl⟩

abbrev Section (N Z : Subgroup E) :=
  derivedNormalSubgroup N ⧸ sectionDenominator N Z

@[expose] def sectionProjection (N Z : Subgroup E) [Z.Normal] :
    derivedNormalSubgroup N →* Section N Z :=
  QuotientGroup.mk' (sectionDenominator N Z)

theorem sectionProjection_surjective (N Z : Subgroup E) [Z.Normal] :
    Function.Surjective (sectionProjection N Z) :=
  QuotientGroup.mk'_surjective (sectionDenominator N Z)

theorem sectionProjection_kernel (N Z : Subgroup E) [Z.Normal] :
    (sectionProjection N Z).ker = sectionDenominator N Z :=
  QuotientGroup.ker_mk' (sectionDenominator N Z)

theorem derivedSeries_range_transport {G : Type v} [Group G] (f : E →* G) (r : ℕ) :
    (derivedSeries E r).map f =
      (derivedSeries f.range r).map f.range.subtype := by
  have h := congrArg (Subgroup.map f.range.subtype)
    (map_derivedSeries_eq (MonoidHom.rangeRestrict_surjective f) r)
  simpa only [Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict] using h

theorem derivedSeries_subgroup_le (A : Subgroup E) (r : ℕ) :
    (derivedSeries A r).map A.subtype ≤ derivedSeries E r :=
  map_derivedSeries_le_derivedSeries A.subtype r

theorem derivedSeries_le_normal_of_quotient (N : Subgroup E) [N.Normal] (r : ℕ)
    (hquotient : derivedSeries (E ⧸ N) r = ⊥) :
    derivedSeries E r ≤ N := by
  have hmap : (derivedSeries E r).map (QuotientGroup.mk' N) = ⊥ := by
    rw [map_derivedSeries_eq (QuotientGroup.mk'_surjective N) r, hquotient]
  simpa only [QuotientGroup.ker_mk'] using
    (Subgroup.map_eq_bot_iff (derivedSeries E r)).mp hmap

theorem derivedSeries_succ_le_derivedNormalSubgroup (N : Subgroup E) [N.Normal] (r : ℕ)
    (hquotient : derivedSeries (E ⧸ N) r = ⊥) :
    derivedSeries E (r + 1) ≤ derivedNormalSubgroup N := by
  rw [derivedSeries_succ, derivedNormalSubgroup_eq]
  exact Subgroup.commutator_mono
    (derivedSeries_le_normal_of_quotient N r hquotient)
    (derivedSeries_le_normal_of_quotient N r hquotient)

end CFSG.ComponentClassification.CatalogueBDerivedNormalSection
