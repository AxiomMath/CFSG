module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Milestones.ASVolI.I3
public import CFSG.GroupTheory.ConjugatePairSubnormality
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitTwoComp
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.HardCentral

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG
open CFSG.ASVolI.ChIJK (IsComponentIn)

theorem isComponentIn_map_subtype {G : Type} [Group G] {M : Subgroup G} {K : Subgroup ↥M}
    (hK : CFSG.IsComponent K) : IsComponentIn (K.map M.subtype) M := by
  have hsg : (K.map M.subtype).subgroupOf M = K :=
    comap_map_eq_self_of_injective M.subtype_injective K
  refine ⟨map_subtype_le K, ?_, ?_⟩
  · exact LocalCores.isQuasisimple_of_mulEquiv
      (K.equivMapOfInjective M.subtype M.subtype_injective) hK.1
  · rw [hsg]
    exact hK.2

theorem isComponentIn_of_le_of_le {G : Type} [Group G] {X Y Q : Subgroup G}
    (hQ : IsComponentIn Q X) (hQY : Q ≤ Y) (hYX : Y ≤ X) : IsComponentIn Q Y := by
  exact ⟨hQY, hQ.2.1, CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hYX hQ.2.2⟩

theorem isComponentIn_subgroupOf_inf {G : Type} [Group G] {K J : Subgroup G} {z : G}
    (hzK : z ∈ K) (hJ : IsComponentIn J (K ⊓ centralizer {z})) :
    IsComponentIn (J.subgroupOf K) (centralizer {(⟨z, hzK⟩ : ↥K)}) := by
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  have hle : J.subgroupOf K ≤ centralizer ({(⟨z, hzK⟩ : ↥K)} : Set ↥K) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hJ.1 hx)).2)
  have hq : IsQuasisimple ↥(J.subgroupOf K) :=
    LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK).symm hJ.2.1
  have hCv : (K ⊓ centralizer ({z} : Set G)).subgroupOf K =
      centralizer ({(⟨z, hzK⟩ : ↥K)} : Set ↥K) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · rintro ⟨-, h⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp h))
    · intro h
      exact ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp h))⟩
  have hsub : ((J.subgroupOf K).subgroupOf
      ((K ⊓ centralizer ({z} : Set G)).subgroupOf K)).IsSubnormal :=
    (CFSG.GroupTheory.isSubnormal_subgroupOf_subgroupOf_iff (B := J)
      (L := K ⊓ centralizer ({z} : Set G)) (K := K) inf_le_left).mpr hJ.2.2
  rw [hCv] at hsub
  exact ⟨hle, hq, hsub⟩

theorem isTwoComponentIn_of_isComponentIn {G : Type} [Group G] [Finite G] {X Q : Subgroup G}
    (hQ : IsComponentIn Q X) (hev : ∃ y ∈ Q, orderOf y = 2) :
    ComponentClassification.HarrisLit.IsTwoComponentIn Q X := by
  obtain ⟨y, hyQ, hy⟩ := hev
  exact ⟨hQ.1, hQ.2.2,
    isTwoQuasisimple_of_involution hQ.2.1 ((Subgroup.orderOf_mk y hyQ).trans hy)⟩

theorem eq_or_le_centralizer_of_isComponentIn {G : Type} [Group G] [Finite G]
    {N K L : Subgroup G} (hK : IsComponentIn K N) (hL : IsComponentIn L N) :
    K = L ∨ K ≤ centralizer (L : Set G) := by
  have hKc : CFSG.IsComponent (K.subgroupOf N) :=
    ⟨LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hK.1).symm hK.2.1,
      hK.2.2⟩
  have hLc : CFSG.IsComponent (L.subgroupOf N) :=
    ⟨LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hL.1).symm hL.2.1,
      hL.2.2⟩
  rcases LocalCores.distinct_components_commute hKc hLc with h | h
  · left
    have hKmap : (K.subgroupOf N).map N.subtype = K := Subgroup.map_subgroupOf_eq_of_le hK.1
    have hLmap : (L.subgroupOf N).map N.subtype = L := Subgroup.map_subgroupOf_eq_of_le hL.1
    rw [← hKmap, ← hLmap, h]
  · right
    have hcomm : ⁅K, L ⊓ N⁆ = ⊥ := LocalCores.commutator_inf_eq_bot_of_subgroupOf hK.1 h
    rw [inf_eq_left.mpr hL.1] at hcomm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm

theorem eq_of_le_of_isSubnormal {G : Type} [Group G] [Finite G] {K A : Subgroup G}
    (hK : CFSG.IsQuasisimple ↥K) (hA : CFSG.IsQuasisimple ↥A) (hAK : A ≤ K)
    (hsub : (A.subgroupOf K).IsSubnormal) : A = K := by
  have hA' : CFSG.IsComponent (A.subgroupOf K) :=
    ⟨LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAK).symm hA, hsub⟩
  have htop : CFSG.IsComponent (⊤ : Subgroup ↥K) :=
    ⟨LocalCores.isQuasisimple_of_mulEquiv (Subgroup.topEquiv (G := ↥K)).symm hK,
      Subgroup.IsSubnormal.top⟩
  rcases LocalCores.distinct_components_commute hA' htop with h | h
  · exact le_antisymm hAK (Subgroup.subgroupOf_eq_top.mp h)
  · exfalso
    have hcenter : A.subgroupOf K ≤ Subgroup.center ↥K :=
      Subgroup.commutator_top_right_eq_bot_iff_le_center.mp h
    have hunit : A.subgroupOf K ≤ Subgroup.centralizer (A.subgroupOf K : Set ↥K) :=
      hcenter.trans (Subgroup.center_le_centralizer _)
    haveI : IsMulCommutative ↥(A.subgroupOf K) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mp hunit
    haveI : Group.IsPerfect ↥(A.subgroupOf K) := hA'.1.1
    haveI : Subsingleton ↥(A.subgroupOf K) := inferInstance
    obtain ⟨a, b, hab⟩ := (CFSG.LocalCores.isQuasisimple_nontrivial hA'.1).exists_pair_ne
    exact hab (Subsingleton.elim a b)

end CFSG.OddStandard.HigherRank.F3
