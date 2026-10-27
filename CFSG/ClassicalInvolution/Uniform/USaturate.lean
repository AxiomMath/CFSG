module

public import CFSG.ClassicalInvolution.Uniform.UTwin
public import CFSG.GroupTheory.SubnormalJoin

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ComponentClassification
open scoped MatrixGroups

namespace IsClassicalMemberU

variable {t : MemberType} {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem isSubnormal_sup_oddCoreIn (hK : IsSubnormal K (Subgroup.centralizer ({z} : Set G))) :
    IsSubnormal (K ⊔ Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)))
      (Subgroup.centralizer ({z} : Set G)) := by
  set C := Subgroup.centralizer ({z} : Set G) with hC
  have hKC : K ≤ C := isSubnormal_le hK
  have hNsub : IsSubnormal (Balance.oddCoreIn C) C := Balance.isSubnormal_oddCoreIn C
  have hNC : Balance.oddCoreIn C ≤ C := Balance.oddCoreIn_le C
  have a₁ := isSubnormal_subgroupOf_top hK
  have a₂ := isSubnormal_subgroupOf_top hNsub
  have hj := CFSG.GroupTheory.isSubnormal_sup
    (Components.mathlib_subnormal_of_chain a₁ Subgroup.IsSubnormal.top)
    (Components.mathlib_subnormal_of_chain a₂ Subgroup.IsSubnormal.top)
  have := Components.chain_map C.subtype (Components.chain_of_mathlib_subnormal hj)
  rwa [Subgroup.map_top, Subgroup.range_subtype, Subgroup.map_sup,
    Subgroup.map_subgroupOf_eq_of_le hKC, Subgroup.map_subgroupOf_eq_of_le hNC] at this

theorem saturate (h : IsClassicalMemberU t K z) (hs : t.IsSolvableType) :
    IsClassicalMemberU t (K ⊔ Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G))) z ∧
      IsIntrinsicU t (K ⊔ Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G))) z := by
  set C := Subgroup.centralizer ({z} : Set G) with hC
  set N := Balance.oddCoreIn C with hN
  have hKC : K ≤ C := h.le_centralizer
  have hNC : N ≤ C := Balance.oddCoreIn_le C
  have hKS : K ⊔ N ≤ C := sup_le hKC hNC
  have hsub : IsSubnormal (K ⊔ N) C := isSubnormal_sup_oddCoreIn h.subnormal
  refine ⟨⟨h.admissible, h.orderOf_eq_two, (le_sup_left : K ≤ K ⊔ N) h.mem, hsub, ?_,
    fun hns => absurd hs hns⟩, fun _ => le_sup_right⟩
  set π := QuotientGroup.mk' (classicalInvolutionOddCore C) with hπ
  have hmap : ((K ⊔ N).subgroupOf C).map π = (K.subgroupOf C).map π := by
    have hN' : N.subgroupOf C = classicalInvolutionOddCore C := by
      ext x
      constructor
      · intro hx
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_subgroupOf.mp hx
        have : y = x := Subtype.ext hyx
        rwa [← this]
      · intro hx
        exact Subgroup.mem_subgroupOf.mpr ⟨x, hx, rfl⟩
    have hsup : (K ⊔ N).subgroupOf C = K.subgroupOf C ⊔ N.subgroupOf C := by
      apply Subgroup.map_injective C.subtype_injective
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hKC,
        Subgroup.map_subgroupOf_eq_of_le hNC, Subgroup.map_subgroupOf_eq_of_le hKS]
    rw [hsup, Subgroup.map_sup, hN']
    have : (classicalInvolutionOddCore C).map π = ⊥ :=
      (Subgroup.map_eq_bot_iff _).mpr (by rw [hπ, QuotientGroup.ker_mk'])
    rw [this, sup_bot_eq]
  obtain ⟨e⟩ := nonempty_oddCoreQuotientEquiv_of_map_eq (isSubnormal_subgroupOf_top hsub)
    (isSubnormal_subgroupOf_top h.subnormal) hmap
  have q : ↥K ⧸ classicalInvolutionOddCore ↥K ≃* ↥(K ⊔ N) ⧸ classicalInvolutionOddCore ↥(K ⊔ N) :=
    (quotEquivSubgroupOf hKC).symm.trans (e.symm.trans (quotEquivSubgroupOf hKS))
  exact MemberType.Witness.of_quotientEquiv q h.witness

end IsClassicalMemberU

end CFSG.ClassicalInvolution.Uniform
