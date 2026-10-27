module

public import CFSG.FeitThompson.Definitions.PuigSubgroupIteration
public import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Solvable
import CFSG.FeitThompson.Local.PuigSylowPrimeCoreInterlace
import CFSG.FeitThompson.Local.PuigSeriesContainsCentralizer

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {G : Type*} [Group G] {p : ℕ}

theorem map_inf_centralizer_subtype {H : Subgroup G} (A : Subgroup H) :
    (A ⊓ centralizer (A : Set H)).map H.subtype
      = A.map H.subtype ⊓ centralizer ((A.map H.subtype : Subgroup G) : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyA, hyc⟩ := mem_inf.1 hy
    refine mem_inf.2 ⟨mem_map_of_mem _ hyA, mem_centralizer_iff.2 ?_⟩
    rintro g hg
    obtain ⟨z, hz, rfl⟩ := hg
    simpa using congrArg Subtype.val (mem_centralizer_iff.1 hyc z hz)
  · intro hx
    obtain ⟨hxA, hxc⟩ := mem_inf.1 hx
    obtain ⟨y, hy, rfl⟩ := hxA
    refine mem_map_of_mem _ (mem_inf.2 ⟨hy, mem_centralizer_iff.2 fun z hz => ?_⟩)
    exact Subtype.ext (by
      simpa using mem_centralizer_iff.1 hxc (z : G) (mem_map_of_mem H.subtype hz))

theorem map_puigCenter_subtype (H : Subgroup G) :
    (puigCenter H).map H.subtype
      = (puigSubgroup H).map H.subtype
        ⊓ centralizer (((puigSubgroup H).map H.subtype : Subgroup G) : Set G) := by
  rw [puigCenter_eq_inf_centralizer, map_inf_centralizer_subtype]

theorem map_puigCenter_sylow_le_map_puigCenter_pCore [Finite G] [Group.IsSolvable G]
    (hp : p.Prime) (hpodd : Odd p) (hGodd : Odd (Nat.card G)) (hp' : pComplCore p G = ⊥)
    (S : Sylow p G) :
    (puigCenter (S : Subgroup G)).map (S : Subgroup G).subtype
      ≤ (puigCenter (pCore p G)).map (pCore p G).subtype := by
  obtain ⟨hlow, -, hup⟩ := puig_pCore_sylow_interlace hp hpodd hGodd hp' S
  rw [map_puigCenter_subtype, map_puigCenter_subtype]
  intro x hx
  obtain ⟨hxL, hxc⟩ := mem_inf.1 hx
  obtain ⟨y, hy, rfl⟩ := hxL
  have hyc : y ∈ centralizer ((puigLower (S : Subgroup G) : Subgroup (S : Subgroup G)) :
      Set (S : Subgroup G)) := by
    refine mem_centralizer_iff.2 fun z hz => Subtype.ext ?_
    simpa using mem_centralizer_iff.1 hxc (z : G)
      (mem_map_of_mem (S : Subgroup G).subtype (puigLower_le_puigSubgroup hz))
  have hylow : y ∈ puigLower (S : Subgroup G) :=
    centralizer_puigLower_le hp S.isPGroup' hyc
  have hxT : (S : Subgroup G).subtype y ∈ (puigSubgroup (pCore p G)).map (pCore p G).subtype :=
    map_mono puigLower_le_puigSubgroup (hlow (mem_map_of_mem _ hylow))
  exact mem_inf.2 ⟨hxT, centralizer_le (by exact_mod_cast hup) hxc⟩

end CFSG.FeitThompson

end
