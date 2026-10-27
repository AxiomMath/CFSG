module

public import CFSG.GH74.Uniqueness.Bender.Aut
public import CFSG.GH74.Uniqueness.Bender.Lemma32
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.GH74.Uniqueness.SU.SU0

open Subgroup CFSG.GH74.Uniqueness.Bender
open scoped commutatorElement

theorem eq_bot_of_isPGroup_of_coprime {C : Type*} [Group C] [Finite C] {A B : Subgroup C}
    (hA : IsPGroup 2 A) (hAB : A ≤ B) (hB : Nat.Coprime 2 (Nat.card B)) : A = ⊥ := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hA
  have hdvd : Nat.card A ∣ Nat.card B := Subgroup.card_dvd_of_le hAB
  have hcop : Nat.Coprime 2 (Nat.card A) := Nat.Coprime.coprime_dvd_right hdvd hB
  rw [hn] at hcop
  have hn0 : n = 0 := by
    by_contra h
    have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 h
    exact absurd (Nat.Coprime.eq_one_of_dvd hcop h2) (by norm_num)
  rw [hn0, pow_zero] at hn
  exact Subgroup.eq_bot_of_card_eq A hn

theorem eq_bot_of_normal_coprime {C : Type*} [Group C] [Finite C] (Q K : Subgroup C)
    [Q.Normal] [K.Normal] (hQ : IsPGroup 2 Q) (hc : centralizer (Q : Set C) ≤ Q)
    (hK : Nat.Coprime 2 (Nat.card K)) : K = ⊥ := by
  have h1 : K ⊓ Q = ⊥ := by
    have hA : IsPGroup 2 (K ⊓ Q : Subgroup C) := hQ.to_le inf_le_right
    exact eq_bot_of_isPGroup_of_coprime hA inf_le_left hK
  have h3 : K ≤ centralizer (Q : Set C) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hmem : ⁅k, q⁆ ∈ ⁅K, Q⁆ := Subgroup.commutator_mem_commutator hk hq
    have hle : ⁅K, Q⁆ ≤ K ⊓ Q := Subgroup.commutator_le_inf K Q
    rw [h1] at hle
    have := hle hmem
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this.symm
  have h4 : K ≤ Q := h3.trans hc
  exact eq_bot_of_isPGroup_of_coprime (hQ.to_le h4) le_rfl hK

theorem pPrimeCore_eq_bot_of_centralizer_le {C : Type*} [Group C] [Finite C] (Q : Subgroup C)
    [Q.Normal] (hQ : IsPGroup 2 Q) (hc : centralizer (Q : Set C) ≤ Q) :
    CFSG.pPrimeCore 2 C = ⊥ := by
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro K hK hcop
  exact eq_bot_of_normal_coprime Q K hQ hc hcop

theorem exists_sylow_centralizer
    {K : Type} [Group K] [Finite K] {n i e : ℕ}
    (h : BenderType K n i e) {x : K} (hx : orderOf x = 2) :
    ∃ Q : Sylow 2 K, x ∈ rootCenter (Q : Subgroup K) ∧
      centralizer ({x} : Set K) ≤ borel (Q : Subgroup K) ∧
      Group.IsSolvable ↥(centralizer ({x} : Set K)) := by
  have hp : IsPGroup 2 (Subgroup.zpowers x) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hx]
    simp
  obtain ⟨Q, hxQ⟩ := hp.exists_le_sylow
  obtain ⟨t, hc⟩ := h.exists_benderCore Q
  have hxQ' : x ∈ (Q : Subgroup K) := hxQ (Subgroup.mem_zpowers x)
  have hxB : x ∈ borel (Q : Subgroup K) := le_borel _ hxQ'
  obtain ⟨hle, -, -, -, hsolv, -, -⟩ := h.lemma_3_4_b Q hc.sq_eq_one hc.not_mem ⟨hxB, hx⟩
  exact ⟨Q, (hc.involution_iff.mp ⟨hxB, hx⟩).1, hle, hsolv⟩

theorem isSolvable_centralizer
    {K : Type} [Group K] [Finite K] {n i e : ℕ}
    (h : BenderType K n i e) {x : K} (hx : orderOf x = 2) :
    Group.IsSolvable ↥(centralizer ({x} : Set K)) :=
  (exists_sylow_centralizer h hx).choose_spec.2.2

theorem pPrimeCore_centralizer_eq_bot
    {K : Type} [Group K] [Finite K] {n i e : ℕ}
    (h : BenderType K n i e) {x : K} (hx : orderOf x = 2) :
    CFSG.pPrimeCore 2 ↥(centralizer ({x} : Set K)) = ⊥ := by
  obtain ⟨Q, hxZ, hle, -⟩ := exists_sylow_centralizer h hx
  have hQC : (Q : Subgroup K) ≤ centralizer ({x} : Set K) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ((mem_rootCenter_iff.mp hxZ).2 q hq).symm
  have hnorm : ((Q : Subgroup K).subgroupOf (centralizer ({x} : Set K))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQC).mpr hle
  refine pPrimeCore_eq_bot_of_centralizer_le
    ((Q : Subgroup K).subgroupOf (centralizer ({x} : Set K))) Q.isPGroup'.comap_subtype ?_
  intro c hc
  rw [Subgroup.mem_centralizer_iff] at hc
  rw [Subgroup.mem_subgroupOf]
  have hcK : (c : K) ∈ centralizer ((Q : Subgroup K) : Set K) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have := hc ⟨q, hQC hq⟩ (by rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]; exact hq)
    exact congrArg Subtype.val this
  rw [h.centralizer_sylow_eq Q] at hcK
  exact (mem_rootCenter_iff.mp hcK).1

theorem not_isComponent_of_isSolvable {H : Type*} [Group H] [Group.IsSolvable H]
    (K : Subgroup H) : ¬ CFSG.IsComponent K := by
  intro hK
  have hq := hK.1
  have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥K
  have : Group.IsPerfect ↥K := hq.1
  have h2 : commutator ↥K = ⊤ := Group.IsPerfect.commutator_eq_top
  rw [h2] at h1
  exact lt_irrefl _ h1

end CFSG.GH74.Uniqueness.SU.SU0
