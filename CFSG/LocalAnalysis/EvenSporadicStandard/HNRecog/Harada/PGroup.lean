module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup
open scoped Pointwise

private lemma zpow_two_mul_mem {G : Type*} [Group G] {S : Subgroup G} {u : G}
    (hu2 : u ^ 2 ∈ S) (n : ℤ) : u ^ (2 * n) ∈ S := by
  have hu2z : u ^ (2 : ℤ) ∈ S := by simpa using hu2
  rw [zpow_mul]
  exact zpow_mem hu2z n

theorem exists_isPGroup_gt_of_two_dvd_index {G : Type*} [Group G] [Finite G] {S : Subgroup G}
    (hS : IsPGroup 2 S) (hidx : 2 ∣ S.index) : ∃ Q : Subgroup G, IsPGroup 2 Q ∧ S < Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hSP⟩ := hS.exists_le_sylow
  refine ⟨P, P.isPGroup', lt_of_le_of_ne hSP ?_⟩
  intro hEq
  exact Sylow.not_dvd_index P (hEq ▸ hidx)

theorem exists_mem_normalizer_sq_mem {G : Type*} [Group G] [Finite G] {S Q : Subgroup G}
    (hQ : IsPGroup 2 Q) (hSQ : S < Q) :
    ∃ u ∈ Q, u ∈ normalizer (S : Set G) ∧ u ∉ S ∧ u ^ 2 ∈ S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSQle : S ≤ Q := le_of_lt hSQ
  obtain ⟨q, hqQ, hqS⟩ := IsConcreteLE.exists_of_lt hSQ
  have hS'proper : S.subgroupOf Q < (⊤ : Subgroup ↥Q) := by
    rw [IsConcreteLE.lt_iff_le_and_exists]
    exact ⟨le_top, ⟨⟨q, hqQ⟩, by trivial, fun h => hqS (Subgroup.mem_subgroupOf.mp h)⟩⟩
  haveI : Group.IsNilpotent (↥Q) := IsPGroup.isNilpotent hQ
  have hnc : NormalizerCondition (↥Q) := Group.normalizerCondition_of_isNilpotent (G := ↥Q)
  obtain ⟨-, x, hxnorm, hxS'⟩ :=
    IsConcreteLE.lt_iff_le_and_exists.mp (hnc (S.subgroupOf Q) hS'proper)
  have hxQ : (x : G) ∈ Q := x.2
  have hxnormG : (x : G) ∈ normalizer (S : Set G) := by
    rw [← subgroupOf_normalizer_eq hSQle] at hxnorm
    exact Subgroup.mem_subgroupOf.mp hxnorm
  have hxS : (x : G) ∉ S := fun h => hxS' (Subgroup.mem_subgroupOf.mpr h)
  obtain ⟨a, ha⟩ := hQ x
  have hpow : ∃ k, (x : G) ^ 2 ^ k ∈ S := ⟨a, by
    have hcoe : ((x ^ 2 ^ a : ↥Q) : G) = (x : G) ^ 2 ^ a := by simp
    rw [← hcoe, ha]
    simpa using S.one_mem⟩
  set m := Nat.find hpow with hm_def
  have hm_spec : (x : G) ^ 2 ^ m ∈ S := by
    rw [hm_def]
    exact Nat.find_spec hpow
  have hm_pos : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · exfalso
      exact hxS (by simpa [h0] using hm_spec)
    · exact hpos
  refine ⟨(x : G) ^ 2 ^ (m - 1), ?_, ?_, ?_, ?_⟩
  · exact pow_mem hxQ _
  · exact pow_mem hxnormG _
  · intro hmem
    have hlt : m - 1 < m := Nat.sub_lt (lt_of_lt_of_le Nat.zero_lt_one hm_pos) Nat.zero_lt_one
    exact Nat.find_min hpow (hm_def ▸ hlt) hmem
  · have hpow_eq : ((x : G) ^ 2 ^ (m - 1)) ^ 2 = (x : G) ^ 2 ^ m := by
      rw [← pow_mul]
      conv_rhs => rw [← Nat.sub_add_cancel hm_pos]
      rw [pow_succ]
    rw [hpow_eq]
    exact hm_spec

theorem card_sup_zpowers_of_sq_mem {G : Type*} [Group G] [Finite G] {S : Subgroup G} {u : G}
    (hu : u ∈ normalizer (S : Set G)) (hu' : u ∉ S) (hu2 : u ^ 2 ∈ S) :
    Nat.card ↥(S ⊔ Subgroup.zpowers u) = 2 * Nat.card S := by
  let K : Subgroup G := S ⊔ Subgroup.zpowers u
  have hSle : S ≤ K := le_sup_left
  have hzp : Subgroup.zpowers u ≤ normalizer (S : Set G) := Subgroup.zpowers_le.mpr hu
  have hri : S.relIndex K = 2 := by
    rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
    refine ⟨u, Subgroup.mem_sup_right (Subgroup.mem_zpowers u), hu', ?_⟩
    intro b hbK
    have hb : b ∈ (S : Set G) * (Subgroup.zpowers u : Set G) := by
      rwa [← coe_mul_of_right_le_normalizer_left S (Subgroup.zpowers u) hzp]
    obtain ⟨s, hs, t, ht, hst⟩ := hb
    change t ∈ Subgroup.zpowers u at ht
    rw [Subgroup.mem_zpowers_iff] at ht
    obtain ⟨k, hk⟩ := ht
    rcases Int.even_or_odd k with ⟨n, hn⟩ | ⟨n, hn⟩
    · right
      have hmem : u ^ (n + n) ∈ S := by
        have heq : n + n = 2 * n := by ring
        rw [heq]
        exact zpow_two_mul_mem hu2 n
      rw [← hst, ← hk, hn]
      exact S.mul_mem hs hmem
    · left
      have hmem : u ^ (2 * n + 1 + 1) ∈ S := by
        have heq : 2 * n + 1 + 1 = 2 * (n + 1) := by ring
        rw [heq]
        exact zpow_two_mul_mem hu2 (n + 1)
      rw [← hst, ← hk, hn, mul_assoc, mul_zpow_self]
      exact S.mul_mem hs hmem
  show Nat.card ↥K = 2 * Nat.card S
  rw [← Subgroup.relIndex_mul_card (H := S) (K := K), inf_of_le_left hSle, hri]

theorem card_dvd_of_isPGroup_le {G : Type*} [Group G] [Finite G] {P K : Subgroup G}
    (hP : IsPGroup 2 P) (hPK : P ≤ K) {k m : ℕ} (hK : Nat.card K = 2 ^ k * m) (hm : Odd m) :
    Nat.card P ∣ 2 ^ k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hdiv : 2 ^ n ∣ 2 ^ k * m := by
    rw [← hn, ← hK]
    exact Subgroup.card_dvd_of_le hPK
  have hcop : Nat.Coprime (2 ^ n) m := hm.coprime_two_left.pow_left n
  rw [hn]
  exact hcop.dvd_of_dvd_mul_right hdiv

theorem isPGroup_map_conj {G : Type*} [Group G] {P : Subgroup G} (hP : IsPGroup 2 P) (c : G) :
    IsPGroup 2 (P.map (MulAut.conj c).toMonoidHom) := by
  exact hP.map (MulAut.conj c).toMonoidHom

end CFSG.EvenSporadicStandard.HNRecog.Harada
