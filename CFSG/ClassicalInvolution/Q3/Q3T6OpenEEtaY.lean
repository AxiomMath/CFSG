module

import CFSG.ClassicalInvolution.Q3.TL3S8BC8
import CFSG.ClassicalInvolution.Q3.Q3T6OpenTL3
public import CFSG.ClassicalInvolution.Q3.Q3T6MainData

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups commutatorElement

section EtaY

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G} {S : Sylow 2 G}
  {W L : Subgroup G} {t : G} {V : Subgroup G}

namespace Sec19Data3

variable (hd : Sec19Data3 K z S W)
include hd

theorem inf_sec19Y_eq :
    W ⊓ sec19Y K z = W ⊓ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) :=
  CFSG.ClassicalInvolution.Q3.TightSylowData.inf_sec19Y_eq hd.toTL3

end Sec19Data3

namespace Sec19DataT3

variable (hd : Sec19DataT3 K z S W L t V)
include hd

theorem invol_mem_W {e : G} (heW : e ∈ W) (he2 : e * e = 1) (he1 : e ≠ 1) :
    e = z ∨ e = t ∨ e = t * z :=
  CFSG.ClassicalInvolution.Q3.TightSylowDataT.invol_mem_W hd.toTL3 heW he2 he1

theorem isCyclic_inf_sec19Y : IsCyclic ↥(W ⊓ sec19Y K z) :=
  CFSG.ClassicalInvolution.Q3.TightSylowDataT.isCyclic_inf_sec19Y hd.toTL3

end Sec19DataT3

end EtaY

end CFSG.ClassicalInvolution.Q3.Q3T6
