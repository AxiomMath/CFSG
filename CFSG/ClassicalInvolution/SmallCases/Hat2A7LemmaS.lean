module

public import CFSG.ClassicalInvolution.Balance.Basic
public import CFSG.ClassicalInvolution.LocalComponent.Normalizer
public import CFSG.ClassicalInvolution.SubnormalClosure.Basic

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open
open CFSG.ClassicalInvolution.Balance (oddCoreIn oddCoreIn_le odd_card_oddCoreIn
  conj_mem_oddCoreIn normalizer_oddCoreIn le_oddCoreIn_of_normalizes oddCoreIn_le_of_isSubnormal)
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

theorem le_normalizer_of_isSubnormal_of_perfect_of_normal {K H N : Subgroup G}
    (hK : IsSubnormal K H) (hperf : ⁅K, K⁆ = K) (hNH : N ≤ H) (hN : (N.subgroupOf H).Normal)
    [Group.IsSolvable ↥N] : N ≤ Subgroup.normalizer (K : Set G) := by
  have hKH : K ≤ H := isSubnormal_le hK
  have h1 : IsSubnormal (K.subgroupOf H) (⊤ : Subgroup ↥H) := by
    have h := isSubnormal_subgroupOf hK H
    rwa [Subgroup.subgroupOf_self] at h
  have hperfK : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hperf
  have eK : ↥(K.subgroupOf H) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKH
  have hperf' : Group.IsPerfect ↥(K.subgroupOf H) :=
    Group.IsPerfect.ofSurjective (f := eK.symm.toMonoidHom) eK.symm.surjective
  have h2 : ⁅K.subgroupOf H, K.subgroupOf H⁆ = K.subgroupOf H :=
    Subgroup.isPerfect_iff.mp hperf'
  have eN : ↥N ≃* ↥(N.subgroupOf H) := (Subgroup.subgroupOfEquivOfLe hNH).symm
  have : (N.subgroupOf H).Normal := hN
  have : Group.IsSolvable ↥(N.subgroupOf H) :=
    Group.isSolvable_of_surjective (f := eN.toMonoidHom) eN.surjective
  have h3 := le_normalizer_of_isSubnormal_of_perfect h1 h2 (N.subgroupOf H)
  rw [← Subgroup.subgroupOf_normalizer_eq hKH] at h3
  intro n hn
  exact h3 (show (⟨n, hNH hn⟩ : ↥H) ∈ N.subgroupOf H from hn)

end CFSG.ClassicalInvolution
