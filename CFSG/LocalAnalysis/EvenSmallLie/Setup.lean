module

public import CFSG.Open.StandardComponentRecognitionMilestoneDefs
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
import CFSG.GroupTheory.OddOverlap

public section

namespace CFSG.EvenSmallLie

open Subgroup CFSG.Open

variable {G : Type*} [Group G]

theorem centralizer_le_normalizer_of_standard [Finite G] {L : Subgroup G}
    (hL : standardComponentIsStandard L) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) : centralizer ({t} : Set G) ≤ normalizer (L : Set G) := fun _ hh =>
  hL.2.2.2.1 ▸ StandardSubgroupAPI.mem_of_odd_inf_map_conj_of_commute hL.2.2.1 htC ht
    (mem_centralizer_singleton_iff.mp hh)

theorem conj_mem_centralizer_of_mem_normalizer {L : Subgroup G} {h x : G}
    (hh : h ∈ normalizer (L : Set G)) (hx : x ∈ centralizer (L : Set G)) :
    h * x * h⁻¹ ∈ centralizer (L : Set G) := by
  rw [mem_centralizer_iff] at hx ⊢
  intro l hl
  have hl' : h⁻¹ * l * h ∈ L := by
    have := (mem_normalizer_iff.mp (inv_mem hh) l).mp hl
    simpa using this
  have hc := hx _ hl'
  calc l * (h * x * h⁻¹) = h * ((h⁻¹ * l * h) * x) * h⁻¹ := by group
    _ = h * (x * (h⁻¹ * l * h)) * h⁻¹ := by rw [hc]
    _ = h * x * h⁻¹ * l := by group

theorem mem_centralizer_of_mem_center {L : Subgroup G} {z : L} (hz : z ∈ center L) :
    (z : G) ∈ centralizer (L : Set G) := by
  rw [mem_centralizer_iff]
  intro l hl
  have := (mem_center_iff.mp hz) ⟨l, hl⟩
  exact congrArg Subtype.val this

theorem centralizer_isPGroup_isCyclic_of_center [Finite G] {L : Subgroup G}
    (hL : standardComponentIsStandard L) {z : L} (hzZ : z ∈ center L) (hz : orderOf (z : G) = 2)
    (hcore : standardComponentOddCore (centralizer ({(z : G)} : Set G)) = ⊥)
    (S : Sylow 2 (centralizer (L : Set G))) (hS : IsCyclic S) :
    IsPGroup 2 (centralizer (L : Set G)) ∧ IsCyclic (centralizer (L : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer ({(z : G)} : Set G) with hHdef
  have hzC : (z : G) ∈ centralizer (L : Set G) := mem_centralizer_of_mem_center hzZ
  have hCH : centralizer (L : Set G) ≤ H := fun c hc => mem_centralizer_singleton_iff.mpr
    ((mem_centralizer_iff.mp hc) z z.2).symm
  have hHN : H ≤ normalizer (L : Set G) := centralizer_le_normalizer_of_standard hL hzC hz
  have hnormal : ((centralizer (L : Set G)).subgroupOf H).Normal := by
    constructor
    intro c hc h
    rw [mem_subgroupOf] at hc ⊢
    simpa using conj_mem_centralizer_of_mem_normalizer (hHN h.2) hc
  set K := pPrimeCore 2 ((centralizer (L : Set G)).subgroupOf H) with hKdef
  have hKmap : (K.map ((centralizer (L : Set G)).subgroupOf H).subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hKodd : Odd (Nat.card (K.map ((centralizer (L : Set G)).subgroupOf H).subtype)) := by
    rw [Subgroup.card_map_of_injective ((centralizer (L : Set G)).subgroupOf H).subtype_injective]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp pPrimeCore_coprime_card))
  have hKle : K.map ((centralizer (L : Set G)).subgroupOf H).subtype ≤
      standardComponentOddCore H :=
    le_sSup ⟨hKmap, hKodd⟩
  rw [hcore, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _
    ((centralizer (L : Set G)).subgroupOf H).subtype_injective] at hKle
  have hcoreC : pPrimeCore 2 (centralizer (L : Set G)) = ⊥ := by
    rw [← pPrimeCore_map_iso 2 (subgroupOfEquivOfLe hCH), ← hKdef, hKle, Subgroup.map_bot]
  obtain ⟨hcard, -⟩ := cyclic_sylow_normal_odd_complement S hS
  rw [hcoreC, Subgroup.card_bot] at hcard
  have hdvd : Nat.card S ∣ Nat.card (centralizer (L : Set G)) :=
    Subgroup.card_subgroup_dvd_card _
  have hCS : Nat.card (centralizer (L : Set G)) = Nat.card S := by
    obtain ⟨k, hk⟩ := hdvd
    have hpos : 0 < Nat.card S := Nat.card_pos
    rw [hk, Nat.mul_div_cancel_left _ hpos] at hcard
    rw [hk, ← hcard, mul_one]
  have hStop : (S : Subgroup (centralizer (L : Set G))) = ⊤ :=
    Subgroup.eq_top_of_card_eq _ hCS.symm
  refine ⟨fun x => ?_, ?_⟩
  · have hx : x ∈ (S : Subgroup (centralizer (L : Set G))) := hStop ▸ mem_top x
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨x, hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  · exact (MulEquiv.isCyclic ((MulEquiv.subgroupCongr hStop).trans Subgroup.topEquiv)).mp hS

end CFSG.EvenSmallLie
