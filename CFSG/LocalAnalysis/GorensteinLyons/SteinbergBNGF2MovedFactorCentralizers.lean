module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.Open
open scoped commutatorElement IsMulCommutative
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)

namespace SteinbergBN

variable {G : Type*} [Group G]

abbrev coreEmb (M : Subgroup G) : CFSG.pCore 2 M →* G :=
  M.subtype.comp (CFSG.pCore 2 M).subtype

theorem range_coreEmb (M : Subgroup G) :
    (coreEmb M).range = CFSG.inSubgroup (CFSG.pCore 2) M := by
  rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rfl

theorem coreEmb_conjNormal (M : Subgroup G) (h : M) (x : CFSG.pCore 2 M) :
    coreEmb M (MulAut.conjNormal h x) = (h : G) * coreEmb M x * (h : G)⁻¹ := by
  simp [coreEmb, MulAut.conjNormal_apply]

theorem conj_mem_core (M : Subgroup G) (h : M) {g : G}
    (hg : g ∈ CFSG.inSubgroup (CFSG.pCore 2) M) :
    (h : G) * g * (h : G)⁻¹ ∈ CFSG.inSubgroup (CFSG.pCore 2) M := by
  rw [← range_coreEmb] at hg ⊢
  obtain ⟨x, rfl⟩ := hg
  exact ⟨MulAut.conjNormal h x, coreEmb_conjNormal M h x⟩

theorem le_normalizer_core [Finite G] (M : Subgroup G) :
    M ≤ normalizer (CFSG.inSubgroup (CFSG.pCore 2) M : Set G) := fun h hh =>
  mem_normalizer_fintype fun _ hx => conj_mem_core M ⟨h, hh⟩ hx

theorem map_center_subtype_eq (K : Subgroup G) :
    (center K).map K.subtype = K ⊓ centralizer (K : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, mem_centralizer_iff.mpr fun g hg => ?_⟩
    exact congrArg Subtype.val (mem_center_iff.mp hy ⟨g, hg⟩)
  · rintro ⟨hxK, hx⟩
    refine ⟨⟨x, hxK⟩, mem_center_iff.mpr fun g => Subtype.ext ?_, rfl⟩
    exact mem_centralizer_iff.mp hx g g.2

end SteinbergBN

open SteinbergBN

end CFSG.LocalAnalysis.GorensteinLyons
