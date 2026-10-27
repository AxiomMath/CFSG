module

public import CFSG.GH74.QTGen4.Recog.Ku.RStructD

public section

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

variable {T M H P : Subgroup G} {z : G}

theorem inv_conj_mul_inv_mem_kuV2 (h : KuHyp G T M H P z) {r : G} (hr : r ∈ kuR T M)
    (v : ↥(pCoreOf 2 M)) :
    r⁻¹ * (v : G) * r * (v : G)⁻¹ ∈ kuV2 T M := by
  have hr' : r⁻¹ ∈ kuR T M := (kuR T M).inv_mem hr
  have := h.comm_mem_kuV2_of_V hr' v
  simpa [mul_assoc] using this

end CFSG.GH74.QTGen4.Ku

end
