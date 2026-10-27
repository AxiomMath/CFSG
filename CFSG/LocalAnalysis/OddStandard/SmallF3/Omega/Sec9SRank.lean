module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SDInputs
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec9r_exists_sylow2 [Finite G] {L U : Subgroup G} (hU : U ≤ L) (hp : IsPGroup 2 U) :
    ∃ P : Subgroup G, IsSylow2Of P L ∧ U ≤ P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp' : IsPGroup 2 (U.subgroupOf L) :=
    hp.of_equiv (Subgroup.subgroupOfEquivOfLe hU).symm
  obtain ⟨Q, hUQ⟩ := hp'.exists_le_sylow
  refine ⟨(Q : Subgroup ↥L).map L.subtype, isSylow2Of_map_sylow Q, ?_⟩
  intro u hu
  have huQ : (⟨u, hU hu⟩ : ↥L) ∈ (Q : Subgroup ↥L) :=
    hUQ (by rw [Subgroup.mem_subgroupOf]; exact hu)
  exact Subgroup.mem_map_of_mem L.subtype huQ

theorem sec9r_exists_card_32 [Finite G] {U : Subgroup G} (hp : IsPGroup 2 U)
    (h : 32 ≤ Nat.card U) : ∃ E : Subgroup G, E ≤ U ∧ Nat.card E = 32 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hn5 : 5 ≤ n := by
    by_contra hlt
    have hle4 : n ≤ 4 := by omega
    have h2n : 2 ^ n ≤ 16 := by
      calc 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hle4
        _ = 16 := by norm_num
    omega
  obtain ⟨E, hcard, _, hEU⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le (p := 2) Nat.prime_two (n := 5) (H := ⊥) (L := U)
      (by rw [Subgroup.card_bot]; exact one_dvd _)
      (by rw [hn]; exact pow_dvd_pow 2 hn5) bot_le
  exact ⟨E, hEU, by rw [hcard]; norm_num⟩

theorem sec9r_exists_card_16 [Finite G] {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian 2 E)
    (hc : Nat.card E = 32) {a : G} (ha : a ∈ E) :
    ∃ K : Subgroup G, K ≤ E ∧ a ∈ K ∧ Nat.card K = 16 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha2 : a ^ 2 = 1 := hE.2 a ha
  have hdvd : Nat.card (Subgroup.zpowers a) ∣ 2 ^ 4 := by
    rw [Nat.card_zpowers a]
    exact (orderOf_dvd_of_pow_eq_one ha2).trans (by norm_num)
  have hL : 2 ^ 4 ∣ Nat.card E := by rw [hc]; norm_num
  obtain ⟨K, hcard, hHK, hKE⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le (p := 2) Nat.prime_two (n := 4)
      (H := Subgroup.zpowers a) (L := E) hdvd hL (Subgroup.zpowers_le.mpr ha)
  exact ⟨K, hKE, hHK (Subgroup.mem_zpowers a), by rw [hcard]; norm_num⟩

theorem sec9r_card_le_of_subset_union [Finite G] {B₁ B₂ E : Subgroup G}
    (h₁ : Nat.card B₁ = 16) (h₂ : Nat.card B₂ = 16) (hE : (E : Set G) ⊆ (B₁ : Set G) ∪ B₂) :
    Nat.card E ≤ 31 := by
  have hb₁ : (B₁ : Set G).ncard = 16 := by
    rw [← Nat.card_coe_set_eq]; exact h₁
  have hb₂ : (B₂ : Set G).ncard = 16 := by
    rw [← Nat.card_coe_set_eq]; exact h₂
  have hinter : 1 ≤ ((B₁ : Set G) ∩ (B₂ : Set G)).ncard := by
    have hmem : (1 : G) ∈ (B₁ : Set G) ∩ (B₂ : Set G) := ⟨B₁.one_mem, B₂.one_mem⟩
    have hsub : ({(1 : G)} : Set G) ⊆ (B₁ : Set G) ∩ (B₂ : Set G) := by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hmem
    calc (1 : ℕ) = ({(1 : G)} : Set G).ncard := by simp
      _ ≤ _ := Set.ncard_le_ncard hsub
  have hunion : ((B₁ : Set G) ∪ (B₂ : Set G)).ncard ≤ 31 := by
    have hsum := Set.ncard_union_add_ncard_inter (B₁ : Set G) (B₂ : Set G)
    omega
  calc Nat.card E = (E : Set G).ncard := Nat.card_coe_set_eq (E : Set G)
    _ ≤ ((B₁ : Set G) ∪ (B₂ : Set G)).ncard := Set.ncard_le_ncard hE
    _ ≤ 31 := hunion

theorem asc82RankOm6M_of (hT6 : Asc82Tab6M) : Asc82RankOm6M := by
  intro G _ _ L U hL hUL hUe
  by_contra hle
  simp only [not_le] at hle
  have hU2 : 32 ≤ Nat.card U := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (CFSG.Open.IsElemAbelian.isPGroup hUe).exists_card_eq
    have hn5 : 5 ≤ n := by
      by_contra hlt
      have hle4 : n ≤ 4 := by omega
      have h2n : 2 ^ n ≤ 16 := by
        calc 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hle4
          _ = 16 := by norm_num
      omega
    rw [hn]
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn5
  obtain ⟨P, hP, hUP⟩ := sec9r_exists_sylow2 hUL (CFSG.Open.IsElemAbelian.isPGroup hUe)
  obtain ⟨B₁, B₂, _, hB1, hB2, hall⟩ := hT6.sylow_E16 G L hL P hP
  obtain ⟨E, hEU, hEc⟩ := sec9r_exists_card_32 (CFSG.Open.IsElemAbelian.isPGroup hUe) hU2
  have hEe : CFSG.Open.IsElemAbelian 2 E := CFSG.Open.IsElemAbelian.mono hUe hEU
  have hsub : (E : Set G) ⊆ (B₁ : Set G) ∪ (B₂ : Set G) := by
    intro a ha
    obtain ⟨K, hKE, haK, hKc⟩ := sec9r_exists_card_16 hEe hEc ha
    have hKP : K ≤ P := hKE.trans (hEU.trans hUP)
    have hK4 : IsElemAb2 K 4 := ⟨CFSG.Open.IsElemAbelian.mono hEe hKE, by rw [hKc]; norm_num⟩
    rcases hall K hKP hK4 with h | h
    · exact Or.inl (h ▸ haK)
    · exact Or.inr (h ▸ haK)
  have hB1c : Nat.card B₁ = 16 := (hB1.2.1.2).trans (by norm_num)
  have hB2c : Nat.card B₂ = 16 := (hB2.2.1.2).trans (by norm_num)
  have hle31 := sec9r_card_le_of_subset_union hB1c hB2c hsub
  omega

end CFSG.OddStandard.SmallF3.Omega
