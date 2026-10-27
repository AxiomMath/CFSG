module

public import CFSG.ClassicalInvolution.Q3.Q3T6OpenEBasic
import CFSG.ClassicalInvolution.Q3.TL3S8BEta
import CFSG.ClassicalInvolution.Q3.Q3T6OpenTL3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups

section Eta

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G} {S : Sylow 2 G}
  {W L : Subgroup G} {t : G} {V : Subgroup G}

namespace Sec19DataT3

variable (hd : Sec19DataT3 K z S W L t V)
include hd

theorem mem_W : t ∈ W := hd.leW hd.memT

end Sec19DataT3

namespace Sec19Data3

variable {W : Subgroup G} (hd : Sec19Data3 K z S W)
include hd

theorem le_centralizer_of_mem {u : G} (hu : u ∈ W) : W ≤ Subgroup.centralizer ({u} : Set G) :=
  fun w hw => Subgroup.mem_centralizer_singleton_iff.mpr (hd.comm_of_mem w hw u hu)

end Sec19Data3

namespace Sec19DataT3

variable (hd : Sec19DataT3 K z S W L t V)
include hd

theorem invol_eq_or {η : Set (Subgroup G)} {S' : Sylow 2 G}
    (hη : η ∈ etaSet (CoreAssembly.conjClass K) S')
    (hinv : ∀ s ∈ (S' : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η) (hWη : W = ⨆ U ∈ η, U)
    {A : Subgroup G} (hA : A ∈ η) {J : Subgroup G} (hJ : J ∈ CoreAssembly.conjClass K)
    (hAJ : A ≤ J) {u : G} (hu : IsUniqueInvolution J u) : u = z ∨ u = t ∨ u = t * z :=
  CFSG.ClassicalInvolution.Q3.TightSylowDataT.invol_eq_or hd.toTL3 hη hinv hWη hA hJ hAJ hu

end Sec19DataT3

namespace Sec19DataT3

variable (hd : Sec19DataT3 K z S W L t V)
include hd

theorem exists_conj_eq_mul : ∃ r ∈ (S : Subgroup G) ⊓ K, r * t * r⁻¹ = t * z :=
  CFSG.ClassicalInvolution.Q3.TightSylowDataT.exists_conj_eq_mul hd.toTL3

theorem sup_eq_inf_sup : W = (K ⊓ W) ⊔ V :=
  CFSG.ClassicalInvolution.Q3.TightSylowDataT.sup_eq_inf_sup hd.toTL3

end Sec19DataT3

end Eta

end CFSG.ClassicalInvolution.Q3.Q3T6
