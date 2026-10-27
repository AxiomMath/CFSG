module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Struct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79BA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem sec5o_oddCore_ne_top_of_twoU43 [Finite G] {L : Subgroup G}
    (h : IsTwoU43 (L ⧸ oddCore L)) : oddCore L ≠ ⊤ := by
  intro htop
  haveI : Subsingleton (↥L ⧸ oddCore ↥L) := (QuotientGroup.subsingleton_iff).mpr htop
  haveI : Finite (↥L ⧸ oddCore ↥L) := inferInstance
  have h1 : Nat.card (Subgroup.center (↥L ⧸ oddCore ↥L)) ≤ 1 :=
    Finite.card_le_one_iff_subsingleton.mpr inferInstance
  have h2 : Nat.card (Subgroup.center (↥L ⧸ oddCore ↥L)) = 2 := h.1
  omega

theorem sec5o_oddCoreIn_le_centerIn [Finite G] {L : Subgroup G} (hL : IsOm6Z2 L) :
    oddCoreIn L ≤ centerIn L := by
  have hne : oddCore L ≠ ⊤ := sec5o_oddCore_ne_top_of_twoU43 hL.2
  have hle : oddCore L ≤ center L := oddCore_le_center_of_isQuasisimple hL.1 hne
  unfold oddCoreIn centerIn CFSG.inSubgroup
  exact Subgroup.map_mono hle

theorem sec5_oddCore_comm_L (h36 : Asc82Lemma36) [Finite G] {t : G} {L : Subgroup G}
    (hs : Sec5Setting G t L) :
    ⁅L, oddCoreIn (centralizer ({t} : Set G))⁆ = ⊥ ∧
      oddCoreIn L ≤ oddCoreIn (centralizer ({t} : Set G)) := by
  let C : Subgroup G := centralizer ({t} : Set G)
  let U : Subgroup G := oddCoreIn C
  have hS : Sec3SettingLB G t L := hs.toSec3SettingLB
  have hLC : L ≤ C := hS.component.le
  have hnorm : ∀ c ∈ C, c ∈ normalizer (L : Set G) := sec4_mem_normalizer h36 hS
  have hΩ : IsOm6Z2 L := hs.isOm6Z2
  have hZ : oddCoreIn L ≤ centerIn L := sec5o_oddCoreIn_le_centerIn hΩ
  haveI : Group.IsPerfect ↥L := hΩ.1.1
  have hLU : L ⊓ U ≤ oddCoreIn L := by
    have hUodd : Odd (Nat.card U) := odd_card_oddCoreIn C
    have hodd : Odd (Nat.card (L ⊓ U : Subgroup G)) :=
      hUodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
    refine le_oddCoreIn_of_normal inf_le_left ?_ hodd
    refine (Subgroup.normal_subgroupOf_iff inf_le_left).mpr ?_
    intro x l hx hl
    rw [Subgroup.mem_inf] at hx ⊢
    refine ⟨?_, ?_⟩
    · exact L.mul_mem (L.mul_mem hl hx.1) (L.inv_mem hl)
    · exact conj_mem_oddCoreIn ((Subgroup.le_normalizer (H := C)) (hLC hl)) hx.2
  have hcomm_center : ⁅L, U⁆ ≤ centerIn L := by
    rw [Subgroup.commutator_le]
    intro a ha u hu
    have haU : a * u * a⁻¹ ∈ U :=
      conj_mem_oddCoreIn ((Subgroup.le_normalizer (H := C)) (hLC ha)) hu
    have hua : u * a⁻¹ * u⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hnorm u ((oddCoreIn_normal C).1 hu)) a⁻¹).mp
        (L.inv_mem ha)
    have hmem : ⁅a, u⁆ ∈ L ⊓ U := by
      rw [Subgroup.mem_inf, commutatorElement_def]
      refine ⟨?_, ?_⟩
      · have h := L.mul_mem ha hua
        convert h using 1
        group
      · exact U.mul_mem haU (U.inv_mem hu)
    exact hZ (hLU hmem)
  have hcenter_le_cent : centerIn L ≤ centralizer (L : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact ((sec5_mem_centerIn_iff.mp hx).2 y hy).symm
  have h1 : ⁅⁅L, U⁆, L⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hcomm_center.trans hcenter_le_cent)
  have h2 : ⁅⁅U, L⁆, L⁆ = ⊥ := by
    rw [Subgroup.commutator_comm U L]
    exact h1
  have h3 : ⁅⁅L, L⁆, U⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rw [show ⁅L, L⁆ = L from Subgroup.commutator_eq_self] at h3
  refine ⟨h3, ?_⟩
  have hnormal : (L.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLC).mpr (fun c hc => hnorm c hc)
  exact oddCoreIn_le_of_normal hLC hnormal

end CFSG.OddStandard.SmallF3.Omega
