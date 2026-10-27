
module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ModelF1051Base

public import Certificates.Certificate442004
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ModelT0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TwoCore

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.ComponentClassification.GSThmB

local notation "P45" => Equiv.Perm (Fin 45)
local notation "z0" => Certificates.OmegaT0.z0 ()
local notation "Q0l" => Certificates.OmegaF1051.q0l ()
local notation "CA0" => Certificates.OmegaF1051.centL (elemsT QA45) z0
local notation "CL0" => Certificates.OmegaF1051.centL (elemsT QP45) z0

theorem length_CL0 :
    List.length CL0 = 576 := by
  have h := card_inf_centralizer QP45 QP45_ok z0
  rw [Certificates.certificate442004.card_CP] at h
  exact h.symm

theorem z0_props :
    (z0 * z0 = 1 ∧ z0 ≠ 1) ∧ z0 ∈ QT0.originalSubgroup ∧
      ∀ t ∈ QT0.originalSubgroup, t * z0 = z0 * t :=
  have h := Certificates.certificate442004
  ⟨⟨h.z_sq, h.z_ne⟩, h.z_mem, h.z_comm⟩

theorem orderOf_z0 : orderOf z0 = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact z0_props.1.1) z0_props.1.2

theorem z0_mem_QT0 :
    z0 ∈ QT0.originalSubgroup :=
  z0_props.2.1

theorem z0_mem_centerIn :
    z0 ∈ centerIn QT0.originalSubgroup :=
  mem_centerIn_iff.2 ⟨z0_mem_QT0, fun t ht => (z0_props.2.2 t ht).symm⟩

theorem mem_zpowers_z0 {x : P45} :
    x ∈ zpowers z0 ↔ x = 1 ∨ x = z0 := by
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have h : z0 ^ (k % 2) = z0 ^ k := by
      have := zpow_mod_orderOf z0 k
      rwa [orderOf_z0, Nat.cast_ofNat] at this
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left
      rw [← h, hk, zpow_zero]
    · right
      rw [← h, hk, zpow_one]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact Subgroup.mem_zpowers _

theorem eq_z0_of_mem_centerIn
    {x : P45} (hx : x ∈ centerIn QT0.originalSubgroup) :
    x = 1 ∨ x = z0 := by
  have hle : zpowers z0 ≤ centerIn QT0.originalSubgroup := by
    rw [Subgroup.zpowers_le]
    exact z0_mem_centerIn
  have hcard : Nat.card (zpowers z0) = 2 := by
    rw [Nat.card_zpowers, orderOf_z0]
  have heq : zpowers z0 = centerIn QT0.originalSubgroup :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, card_centerIn_QT0])
  rw [← heq] at hx
  exact mem_zpowers_z0.1 hx

theorem q0l_closed :
    ((Q0l).length = 32 ∧ (Q0l).Nodup) ∧ (1 : P45) ∈ Q0l ∧
      ∀ a ∈ Q0l, a⁻¹ ∈ Q0l ∧ ∀ b ∈ Q0l, a * b ∈ Q0l := by
  have h := Certificates.certificate442004
  have hlen := card_eq_length (fun g : P45 => g ∈ Certificates.OmegaS107.Q0) id
    Function.injective_id Q0l h.nodup_q0l
    (fun b => ⟨fun hb => ⟨b, (h.mem_q0l b).1 hb, rfl⟩,
      fun ⟨a, ha, hab⟩ => hab ▸ (h.mem_q0l a).2 ha⟩)
  refine ⟨⟨hlen.symm.trans h.card_Q0, h.nodup_q0l⟩, (h.mem_q0l 1).2 (one_mem _), fun a ha => ?_⟩
  have ha' := (h.mem_q0l a).1 ha
  exact ⟨(h.mem_q0l _).2 (inv_mem ha'),
    fun b hb => (h.mem_q0l _).2 (mul_mem ha' ((h.mem_q0l b).1 hb))⟩

theorem mem_Q32_iff {g : P45} : g ∈ Q32 ↔ g ∈ Q0l :=
  mem_closure_list_iff (q0l_closed.2.1) (fun a ha => (q0l_closed.2.2 a ha).1)
    (fun a ha b hb => (q0l_closed.2.2 a ha).2 b hb)

theorem mem_Q32_iff_mem_Q0 {g : P45} :
    g ∈ Q32 ↔ g ∈ Certificates.OmegaS107.Q0 :=
  mem_Q32_iff.trans (Certificates.certificate442004.mem_q0l g)

theorem card_Q32 : Nat.card Q32 = 2 ^ 5 := by
  have hc := q0l_closed
  have h := card_eq_length (fun g : P45 => g ∈ Q32) id Function.injective_id Q0l hc.1.2
    (fun b => ⟨fun hb => ⟨b, mem_Q32_iff.2 hb, rfl⟩, fun ⟨a, ha, hab⟩ => hab ▸ mem_Q32_iff.1 ha⟩)
  rw [show Nat.card Q32 = Nat.card {a // a ∈ Q32} from rfl, h, hc.1.1]
  norm_num

theorem isPGroup_Q32 : IsPGroup 2 Q32 :=
  IsPGroup.of_card card_Q32

theorem Q32_le_oTwoC :
    Q32 ≤ oTwoC := fun _ hg =>
  Certificates.certificate442004.le_oTwo (mem_Q32_iff_mem_Q0.1 hg)

theorem mem_normalizer_Q32
    {c : P45} (hc : c ∈ QA45.originalSubgroup) (hz : c * z0 = z0 * c) :
    c ∈ normalizer (Q32 : Set P45) := by
  have hconj : ∀ c' : P45, c' ∈ QA45.originalSubgroup → c' * z0 = z0 * c' →
      ∀ q ∈ Q32, c' * q * c'⁻¹ ∈ Q32 := by
    intro c' hc' hz' q hq
    rw [mem_Q32_iff_mem_Q0] at hq ⊢
    exact Certificates.certificate442004.normal c'
      (Subgroup.mem_inf.2 ⟨hc', Subgroup.mem_centralizer_singleton_iff.2 hz'⟩) q hq
  have hzinv : c⁻¹ * z0 = z0 * c⁻¹ := Commute.inv_left (show Commute c z0 from hz)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hconj c hc hz x hx, fun hx => ?_⟩
  have h := hconj c⁻¹ (inv_mem hc) hzinv _ hx
  simpa [mul_assoc] using h

theorem twoCoreIn_oTwoC
    (h288 : Nat.card ↥oTwoC = 288) : twoCoreIn oTwoC = Q32 := by
  have hle : Q32 ≤ oTwoC := Q32_le_oTwoC
  have hnorm : (Q32.subgroupOf oTwoC).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
    intro x hx
    have hxC : x ∈ QP45.originalSubgroup ⊓ centralizer ({z0} : Set P45) :=
      PspFrame.oTwoRes_le _ hx
    exact mem_normalizer_Q32 (QP45_le_QA45 hxC.1)
      (Subgroup.mem_centralizer_singleton_iff.1 hxC.2)
  have hindex : (Q32.subgroupOf oTwoC).index = 9 := by
    have h := (Q32.subgroupOf oTwoC).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, card_Q32, h288] at h
    omega
  exact twoCoreIn_eq_of_normal_sylow hle isPGroup_Q32 hnorm (by rw [hindex]; norm_num)

end CFSG.OddStandard.SmallF3.Omega
