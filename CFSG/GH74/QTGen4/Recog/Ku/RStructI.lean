module

public import CFSG.GH74.QTGen4.Recog.Ku.Hyp

public section

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

variable {T M H P : Subgroup G} {z : G}

theorem comm_of_mem_pCoreOf (h : KuHyp G T M H P z) {p q : G} (hp : p ∈ pCoreOf 2 M)
    (hq : q ∈ pCoreOf 2 M) : p * q = q * p :=
  congrArg Subtype.val (h.vElem.1.is_comm.comm ⟨p, hp⟩ ⟨q, hq⟩)

end CFSG.GH74.QTGen4.Ku

end
