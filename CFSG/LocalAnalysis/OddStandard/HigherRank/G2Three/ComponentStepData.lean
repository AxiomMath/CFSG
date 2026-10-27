module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Core
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.SU43Transport
public import CFSG.Milestones.ASVolI.I3
public import CFSG.Quasithin.H13.NQBlockEscapingComponent

public section

namespace CFSG.OddStandard.HigherRank.G2Three

open Subgroup

private lemma mem_centralizer_zpowers_iff {H : Type} [Group H] (u c : H) :
    c ∈ Subgroup.centralizer ((Subgroup.zpowers u : Subgroup H) : Set H) ↔ c * u = u * c := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  exact Subgroup.mem_centralizer_singleton_iff

theorem Case3Core.isTwoComponentIn_centralizer {G : Type} [Group G] [Finite G] {z : G}
    {K : Subgroup G} (h : Case3Core G z K) (u : ↥(centralizer ({z} : Set G)))
    (huK : (u : G) ∈ K) (hu4 : orderOf (u : G) = 4)
    (hcomm : ∀ k ∈ K, k * (u : G) = (u : G) * k)
    (htight : centralizer ({(u : G)} : Set G) ≤ normalizer (K : Set G)) :
    IsPGroup 2 (zpowers u) ∧
      CFSG.ASVolI.ChIJK.IsTwoComponentIn (K.subgroupOf (centralizer ({z} : Set G)))
        (centralizer ((zpowers u : Subgroup ↥(centralizer ({z} : Set G))) :
          Set ↥(centralizer ({z} : Set G)))) := by
  have hP : IsPGroup 2 (Subgroup.zpowers u) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Nat.card_zpowers, (Subgroup.orderOf_coe u).symm.trans hu4]
    norm_num
  refine ⟨hP, ?_⟩
  let X : Subgroup G := centralizer ({z} : Set G)
  let L : Subgroup ↥X := K.subgroupOf X
  let C : Subgroup ↥X := centralizer ((Subgroup.zpowers u : Subgroup ↥X) : Set ↥X)
  change CFSG.ASVolI.ChIJK.IsTwoComponentIn L C
  unfold CFSG.ASVolI.ChIJK.IsTwoComponentIn CFSG.ASVolI.ChIJK.IsCComponentIn
  have hLC : L ≤ C := by
    intro k hk
    change k ∈ K.subgroupOf X at hk
    change k ∈ Subgroup.centralizer ((Subgroup.zpowers u : Subgroup ↥X) : Set ↥X)
    rw [mem_centralizer_zpowers_iff]
    exact Subtype.ext (hcomm (k : G) (Subgroup.mem_subgroupOf.mp hk))
  have hnorm : (L.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hLC]
    intro a k ha hk
    change k ∈ Subgroup.centralizer ((Subgroup.zpowers u : Subgroup ↥X) : Set ↥X) at hk
    change k * a * k⁻¹ ∈ K.subgroupOf X
    rw [Subgroup.mem_subgroupOf]
    have hku : k * u = u * k := (mem_centralizer_zpowers_iff u k).mp hk
    have hkuG : (k : G) * (u : G) = (u : G) * (k : G) :=
      congrArg (fun x : ↥X => (x : G)) hku
    have hcCent : (k : G) ∈ Subgroup.centralizer ({(u : G)} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hkuG
    have hcNorm : (k : G) ∈ Subgroup.normalizer (K : Set G) := htight hcCent
    have haK : (a : G) ∈ K := by
      change a ∈ K.subgroupOf X at ha
      exact Subgroup.mem_subgroupOf.mp ha
    have hmem : (k : G) * (a : G) * (k : G)⁻¹ ∈ K :=
      ((Subgroup.mem_normalizer_iff.mp hcNorm) (a : G)).mp haK
    simpa using hmem
  have hLquasi : CFSG.IsQuasisimple ↥L :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe h.le_centralizer).symm h.quasisimple
  have hcompQuasi : CFSG.IsQuasisimple ↥(L.subgroupOf C) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hLC).symm hLquasi
  have hcomp : CFSG.IsComponent (L.subgroupOf C) := ⟨hcompQuasi, hnorm.isSubnormal⟩
  have hCComp : CFSG.IsCComponent (L.subgroupOf C) :=
    CFSG.Quasithin.H13.NQBlock.isCComponent_of_isComponent hcomp
  have hSU : IsSU43 (↥L ⧸ CFSG.oddCore ↥L) :=
    isSU43_quotient_oddCore_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h.le_centralizer)
      h.quotient
  exact ⟨⟨hLC, hCComp⟩, hSU.1⟩

end CFSG.OddStandard.HigherRank.G2Three
