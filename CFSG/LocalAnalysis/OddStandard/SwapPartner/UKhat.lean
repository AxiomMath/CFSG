module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTwoRoot
import CFSG.LocalAnalysis.OddStandard.SwapPartner.TwKhat

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup

open scoped commutatorElement

theorem exists_khat {G : Type} [Group G] {x : G} {A : Subgroup G}
    (hAx : A ≤ centralizer ({x} : Set G)) (hA : Group.IsPerfect ↥A)
    {K : Subgroup (TwoSec x)} [K.Normal] (hKq : CFSG.IsQuasisimple ↥K)
    (hAK : (A.subgroupOf (centralizer ({x} : Set G))).map
      (QuotientGroup.mk' (zpowers (selfC x))) ≤ K) :
    ∃ Kh : Subgroup G, Kh ≤ centralizer ({x} : Set G) ∧
      (Kh.subgroupOf (centralizer ({x} : Set G))).Normal ∧ ⁅Kh, Kh⁆ = Kh ∧
      CFSG.Open.IsQuasisimple ↥Kh ∧ A ≤ Kh ∧
      Nonempty (↥Kh ⧸ center ↥Kh ≃* ↥K ⧸ center ↥K) := by
  let H := centralizer ({x} : Set G)
  let KH : Subgroup H := hatSub (selfC x) K
  have hKperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hKq.1
  have hxc : ∀ h : H, h * selfC x = selfC x * h :=
    fun h => Subgroup.mem_center_iff.mp (selfC_mem_center x) h
  have hKHperf : ⁅KH, KH⁆ = KH := hatSub_perfect (x := selfC x) hxc hKperf
  have hAperf : ⁅A.subgroupOf H, A.subgroupOf H⁆ = A.subgroupOf H := by
    apply (Subgroup.map_subtype_inj (H := H)).mp
    rw [Subgroup.map_commutator (A.subgroupOf H) (A.subgroupOf H) H.subtype,
      Subgroup.map_subgroupOf_eq_of_le hAx, Subgroup.isPerfect_iff.mp hA]
  have hA'KH : A.subgroupOf H ≤ KH :=
    le_hatSub_of_perfect (x := selfC x) hAperf (Subgroup.map_le_iff_le_comap.mp hAK)
  have hKhperf : ⁅KH.map H.subtype, KH.map H.subtype⁆ = KH.map H.subtype := by
    rw [← Subgroup.map_commutator KH KH H.subtype, hKHperf]
  obtain ⟨eK⟩ := nonempty_quotient_center_equiv (H := ↥H) (x := selfC x) hxc hKperf
  let eKH : ↥KH ≃* ↥(KH.map H.subtype) :=
    Subgroup.equivMapOfInjective KH H.subtype H.subtype_injective
  have hcenter : (center ↥KH).map (eKH : ↥KH →* ↥(KH.map H.subtype)) =
      center ↥(KH.map H.subtype) := Subgroup.map_center_eq eKH
  let eQ : (↥KH ⧸ center ↥KH) ≃*
      (↥(KH.map H.subtype) ⧸ center ↥(KH.map H.subtype)) :=
    QuotientGroup.congr (center ↥KH) (center ↥(KH.map H.subtype)) eKH hcenter
  let e : (↥(KH.map H.subtype) ⧸ center ↥(KH.map H.subtype)) ≃*
      (↥K ⧸ center ↥K) := eQ.symm.trans eK
  have hOpen : CFSG.Open.IsQuasisimple ↥(KH.map H.subtype) := by
    refine ⟨Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hKhperf), ?_⟩
    letI : IsSimpleGroup (↥K ⧸ center ↥K) := hKq.2.1
    exact e.isSimpleGroup
  refine ⟨KH.map H.subtype, Subgroup.map_subtype_le KH, ?_, hKhperf, hOpen, ?_, ⟨e⟩⟩
  · show ((KH.map H.subtype).subgroupOf H).Normal
    have heq : (KH.map H.subtype).subgroupOf H = KH :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective KH
    rw [heq]
    exact hatSub_normal
  · have h1 : (A.subgroupOf H).map H.subtype ≤ KH.map H.subtype := Subgroup.map_mono hA'KH
    rwa [Subgroup.map_subgroupOf_eq_of_le hAx] at h1

end CFSG.OddStandard.AltStdSec.SwapPartner
