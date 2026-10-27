module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PCMap
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PFbar

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec63PC_factAt_of_fact [Finite G] {P : Type} [Group P] (f : P →* G)
    (hf : Function.Injective f) (α : MulAut P) (s : G)
    (hfix : (fixSub α).map f = f.range ⊓ centralizer ({s} : Set G))
    (h : Sec63PCFact f.range s) : Sec63PTFactAt P α := by
  intro V hV hL b hb hb2
  have hV' : IsComponentIn (V.map f) (f.range ⊓ centralizer ({s} : Set G)) := by
    rw [← hfix]
    exact (sec63PT_isComponentIn_map_iff f hf).mpr hV
  have hL' : IsL29 (V.map f) := (sec63PT_isL29_map_iff f hf).mpr hL
  have hfb : f b ∈ V.map f := Subgroup.mem_map.mpr ⟨b, hb, rfl⟩
  have hfb2 : orderOf (f b) = 2 := by
    rw [orderOf_injective f hf b, hb2]
  have hres : Sec63PCAt f.range (V.map f) (f b) := h (V.map f) hV' hL' (f b) hfb hfb2
  rw [MonoidHom.range_eq_map] at hres
  have htop : Sec63PCAt (⊤ : Subgroup P) V b := (sec63PC_at_map_iff f hf).mp hres
  unfold Sec63PCAt at htop
  rw [top_inf_eq] at htop
  exact htop

end CFSG.OddStandard.SmallF3.Omega
