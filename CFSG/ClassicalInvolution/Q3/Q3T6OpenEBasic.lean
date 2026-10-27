module

public import CFSG.ClassicalInvolution.Q3.Q3T6MainSylow
import CFSG.ClassicalInvolution.Q3.Q3T6OpenTL3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups

section Basic

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

namespace TightStd3

variable (ht : TightStd3 K z)
include ht

theorem hypGen : HypOmegaGen (CoreAssembly.conjClass K) :=
  hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) ht.hyp

theorem conjSub_eq_conjSub {a b : G} (h : a * z * a⁻¹ = b * z * b⁻¹) :
    conjSub a K = conjSub b K :=
  CFSG.ClassicalInvolution.Q3.TightMemStd.conjSub_eq_conjSub ht.toTL3 h

theorem exists_isUniqueInvolution_member {J : Subgroup G} (hJ : J ∈ CoreAssembly.conjClass K) :
    ∃ u : G, IsUniqueInvolution J u :=
  CFSG.ClassicalInvolution.Q3.TightMemStd.exists_isUniqueInvolution_member ht.toTL3 hJ

theorem eq_of_isUniqueInvolution_member {J₁ J₂ : Subgroup G} (h₁ : J₁ ∈ CoreAssembly.conjClass K)
    (h₂ : J₂ ∈ CoreAssembly.conjClass K) {u : G} (hu₁ : IsUniqueInvolution J₁ u)
    (hu₂ : IsUniqueInvolution J₂ u) : J₁ = J₂ :=
  CFSG.ClassicalInvolution.Q3.TightMemStd.eq_of_isUniqueInvolution_member ht.toTL3 h₁ h₂ hu₁ hu₂

theorem normalizer_eq_centralizer_member {J : Subgroup G} (hJ : J ∈ CoreAssembly.conjClass K)
    {u : G} (hu : IsUniqueInvolution J u) :
    Subgroup.normalizer (J : Set G) = Subgroup.centralizer ({u} : Set G) :=
  le_antisymm (S1911.normalizer_le_centralizer_member hu)
    (ht.centralizer_le_normalizer_member hJ hu)

end TightStd3

namespace Sec19Data3

variable {S : Sylow 2 G} {W : Subgroup G} (hd : Sec19Data3 K z S W)
include hd

theorem comm_of_mem : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x :=
  CFSG.ClassicalInvolution.Q3.TightSylowData.comm_of_mem hd.toTL3

end Sec19Data3

end Basic

end CFSG.ClassicalInvolution.Q3.Q3T6
