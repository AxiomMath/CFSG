module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC0A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private theorem conj_mem_L (h : Hyp G t L) {g : G} (hg : g ∈ invCent t) {x : G} (hx : x ∈ L) :
    g * x * g⁻¹ ∈ L := by
  have hxH : x ∈ invCent t := L_le_invCent h hx
  have hmem : (⟨g, hg⟩ : ↥(invCent t)) * (⟨x, hxH⟩ : ↥(invCent t)) *
      (⟨g, hg⟩ : ↥(invCent t))⁻¹ ∈ L.subgroupOf (invCent t) :=
    h.normal.conj_mem ⟨x, hxH⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨g, hg⟩
  simpa using (Subgroup.mem_subgroupOf.mp hmem)

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
