module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCGCoreOrthogonal
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBLSmallBinaryOrthogonal

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.RankThree.GroupTheory.SteinbergBY SteinbergCG
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)
open TauCeti.QuadraticMap (orthogonalGroup)
open scoped commutatorElement IsMulCommutative

namespace SteinbergCG

section Transport

variable {H G : Type*} [Group H] [Group G] {f : H →* G} {B : Subgroup H}

theorem map_comap_inf_of_le_map {S : Subgroup G} (hS : S ≤ B.map f) :
    (S.comap f ⊓ B).map f = S := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (mem_inf.mp hx).1
  · intro s hs
    obtain ⟨b, hb, rfl⟩ := hS hs
    exact ⟨b, mem_inf.mpr ⟨hs, hb⟩, rfl⟩

end Transport

end SteinbergCG

end CFSG.LocalAnalysis.GorensteinLyons
