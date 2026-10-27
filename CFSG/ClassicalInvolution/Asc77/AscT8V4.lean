module

import CFSG.ClassicalInvolution.Asc77.AscOddCoreNormalEng
public import CFSG.ClassicalInvolution.Asc77.AscT8S26UAction
public import CFSG.ClassicalInvolution.Asc77.AscT8Y1

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

namespace T8V

section Img

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem le_oddCoreOf_of_normal_odd' {M N : Subgroup G} (hNM : N ≤ M)
    (hn : M ≤ Subgroup.normalizer (N : Set G)) (hodd : Odd (Nat.card N)) : N ≤ oddCoreOf M :=
  CFSG.ClassicalInvolution.Asc77.AscFusion.le_oddCoreOf_of_normal_odd_gen hNM hn hodd

theorem comm_mem_oddCoreOf_layerRes {a y : G} {M : Subgroup G} (hy : y ∈ T8.cenZ a)
    (hyN : y ∈ Subgroup.normalizer (M : Set G))
    (hcomm : ∀ k ∈ M, ⁅y, k⁆ ∈ oddCoreOf M) {k : G} (hk : k ∈ T8.layerRes a M) :
    ⁅y, k⁆ ∈ oddCoreOf (T8.layerRes a M) := by
  have hLM : T8.layerRes a M ≤ M := T8.layerRes_le a M
  have hyL : y ∈ Subgroup.normalizer (T8.layerRes a M : Set G) := T8.mem_normalizer_layerRes hyN hy
  set N : Subgroup G := oddCoreOf M ⊓ T8.layerRes a M with hN
  have hNL : N ≤ T8.layerRes a M := inf_le_right
  have hnorm : T8.layerRes a M ≤ Subgroup.normalizer (N : Set G) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro n
    have hu' : u ∈ M := hLM hu
    have h1 := mem_normalizer_oddCoreOf hu'
    constructor
    · rintro ⟨hn1, hn2⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp h1 n).mp hn1, ?_⟩
      exact (T8.layerRes a M).mul_mem ((T8.layerRes a M).mul_mem hu hn2)
        ((T8.layerRes a M).inv_mem hu)
    · rintro ⟨hn1, hn2⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp h1 n).mpr hn1, ?_⟩
      have := (T8.layerRes a M).mul_mem
        ((T8.layerRes a M).mul_mem ((T8.layerRes a M).inv_mem hu) hn2) hu
      simpa [mul_assoc] using this
  have hodd : Odd (Nat.card N) :=
    (oddCoreOf_odd_natCard M).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hmem : ⁅y, k⁆ ∈ N := by
    refine ⟨hcomm k (hLM hk), ?_⟩
    have h1 : y * k * y⁻¹ ∈ T8.layerRes a M :=
      (Subgroup.mem_normalizer_iff.mp hyL k).mp hk
    rw [commutatorElement_def]
    exact (T8.layerRes a M).mul_mem h1 ((T8.layerRes a M).inv_mem hk)
  exact le_oddCoreOf_of_normal_odd' hNL hnorm hodd hmem

theorem mk_mem_oddCoreOf_layerImg {a : G} {M : Subgroup G} (hM : T8.XMem Ω a M)
    (c : ↥(T8.layerJoin Ω a)) (hc : (c : G) ∈ oddCoreOf (T8.layerRes a M)) :
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(T8.layerJoin Ω a)) c :
        T8.LayerQuot Ω a) ∈ oddCoreOf (T8.layerImg Ω a M) := by
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥(T8.layerJoin Ω a))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  have hLY : T8.layerRes a M ≤ T8.layerJoin Ω a := T8.le_layerJoin ⟨M, hM, rfl⟩
  have h1 : c ∈ oddCoreOf ((T8.layerRes a M).subgroupOf (T8.layerJoin Ω a)) := by
    rw [oddCoreOf_subgroupOf hLY]
    exact hc
  have h2 := oddCoreOf_map_mk_of_odd (K := (T8.layerRes a M).subgroupOf (T8.layerJoin Ω a))
    (X := classicalInvolutionOddCore ↥(T8.layerJoin Ω a)) (odd_natCard_inf hodd _)
  unfold T8.layerImg
  rw [h2]
  exact Subgroup.mem_map_of_mem _ h1

theorem s26Act_mul_inv_mem (hΩ : HypOmegaMod p f Ω) {a y : G} {M : Subgroup G}
    (hM : T8.XMem Ω a M) (hy : y ∈ T8.cenZ a) (hyN : y ∈ Subgroup.normalizer (M : Set G))
    (hcomm : ∀ k ∈ M, ⁅y, k⁆ ∈ oddCoreOf M) :
    ∀ kb ∈ T8.layerImg Ω a M,
      s26Act (T8.layerJoin Ω a) ⟨y, mem_normalizer_iff_conjSub_eq.mpr
        (T8.layerJoin_conjSub_eq hΩ hy)⟩ kb * kb⁻¹ ∈ oddCoreOf (T8.layerImg Ω a M) := by
  intro kb hkb
  obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.mp hkb
  have hyY : y ∈ Subgroup.normalizer ((T8.layerJoin Ω a : Subgroup G) : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (T8.layerJoin_conjSub_eq hΩ hy)
  have hkL : (k' : G) ∈ T8.layerRes a M := Subgroup.mem_subgroupOf.mp hk'
  have hyk : y * (k' : G) * y⁻¹ ∈ T8.layerJoin Ω a :=
    (Subgroup.mem_normalizer_iff.mp hyY (k' : G)).mp k'.2
  have e := s26Act_mk (T8.layerJoin Ω a) ⟨y, hyY⟩ k' ⟨y * (k' : G) * y⁻¹, hyk⟩ rfl
  have hc : ((⟨y * (k' : G) * y⁻¹, hyk⟩ * k'⁻¹ : ↥(T8.layerJoin Ω a)) : G) =
      ⁅y, (k' : G)⁆ := by
    simp [commutatorElement_def]
  have h3 := mk_mem_oddCoreOf_layerImg hM (⟨y * (k' : G) * y⁻¹, hyk⟩ * k'⁻¹)
    (by rw [hc]; exact comm_mem_oddCoreOf_layerRes hy hyN hcomm hkL)
  change s26Act (T8.layerJoin Ω a) ⟨y, hyY⟩ (QuotientGroup.mk k') * (QuotientGroup.mk k')⁻¹ ∈ _
  rw [e]
  simpa [QuotientGroup.mk'_apply, map_mul, map_inv] using h3

theorem comm_mk_mem {a : G} {M : Subgroup G} (hM : T8.XMem Ω a M)
    (e : ↥(T8.layerJoin Ω a)) (hy : (e : G) ∈ T8.cenZ a)
    (hyN : (e : G) ∈ Subgroup.normalizer (M : Set G))
    (hcomm : ∀ k ∈ M, ⁅(e : G), k⁆ ∈ oddCoreOf M) :
    ∀ kb ∈ T8.layerImg Ω a M,
      ⁅(QuotientGroup.mk' (classicalInvolutionOddCore ↥(T8.layerJoin Ω a)) e :
        T8.LayerQuot Ω a), kb⁆ ∈ oddCoreOf (T8.layerImg Ω a M) := by
  intro kb hkb
  obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.mp hkb
  have hkL : (k' : G) ∈ T8.layerRes a M := Subgroup.mem_subgroupOf.mp hk'
  have h3 := mk_mem_oddCoreOf_layerImg hM ⁅e, k'⁆
    (by
      have : ((⁅e, k'⁆ : ↥(T8.layerJoin Ω a)) : G) = ⁅(e : G), (k' : G)⁆ := by
        simp [commutatorElement_def]
      rw [this]
      exact comm_mem_oddCoreOf_layerRes hy hyN hcomm hkL)
  rwa [map_commutatorElement] at h3

end Img

end T8V

end CFSG.ClassicalInvolution.Asc77
