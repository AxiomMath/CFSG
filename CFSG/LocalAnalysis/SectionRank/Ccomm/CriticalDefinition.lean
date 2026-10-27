module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical

public section

namespace CFSG.SectionRank.Ccomm

open Subgroup

variable {G : Type*} [Group G]

abbrev ThompsonCritical (C : Subgroup G) : Prop := IsThompsonCritical C

theorem map_center_subtype (C : Subgroup G) :
    (center C).map C.subtype = C ⊓ centralizer (C : Set G) := by
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c.2, mem_centralizer_iff.mpr fun y hy => ?_⟩
    have := mem_center_iff.mp hc ⟨y, hy⟩
    exact congrArg Subtype.val this
  · rintro ⟨hxC, hx⟩
    refine ⟨⟨x, hxC⟩, mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩
    exact (mem_centralizer_iff.mp hx y y.2)

theorem thompsonCritical_iff (C : Subgroup G) :
    ThompsonCritical C ↔ C.Characteristic ∧
      (frattini C).map C.subtype ≤ (center C).map C.subtype ∧
      ⁅(⊤ : Subgroup G), C⁆ ≤ (center C).map C.subtype ∧
      centralizer (C : Set G) = (center C).map C.subtype := by
  rw [map_center_subtype]
  rfl

end CFSG.SectionRank.Ccomm
