module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Centralizer

public section

namespace CFSG.OddStandard.L2Ree

open Subgroup CFSG.EvenSporadicStandard

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma factorization_two_mul_odd {w : ℕ} (hw : Odd w) : (2 * w).factorization 2 = 1 := by
  have hw0 : w ≠ 0 := by rintro rfl; exact hw.not_two_dvd_nat (dvd_zero 2)
  rw [Nat.factorization_mul (by norm_num) hw0, Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd hw.not_two_dvd_nat, add_zero]

theorem exists_centralizer_eq_prod_of_odd_out (h : StdHyp G L)
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {t : G}
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hodd : Odd (MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)).range.index)
    (hZ : center L = ⊥) :
    ∃ M : Subgroup G, L ≤ M ∧ (L.subgroupOf M).Normal ∧ Odd (L.relIndex M) ∧
      centralizer ({t} : Set G) = M ⊔ zpowers t ∧ Disjoint M (zpowers t) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup G := centralizer ({t} : Set G) with hHdef
  have hHN : H ≤ normalizer (L : Set G) := by
    rw [hHdef]
    exact h.centralizer_le_normalizer ht ht2
  have hLH : L ≤ H := fun l hl =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 ht l hl)
  have htH : t ∈ H := mem_centralizer_singleton_iff.2 rfl
  have hzH : zpowers t ≤ H := zpowers_le.2 htH
  have hd : Disjoint L (zpowers t) :=
    disjoint_of_le_centralizer_of_center_eq_bot (zpowers_le.2 ht) hZ
  have htL : t ∉ L := by
    intro htL
    have ht1 : t = 1 := (Subgroup.disjoint_def.mp hd) htL (mem_zpowers t)
    rw [ht1, orderOf_one] at ht2
    omega
  set K : Subgroup G := L ⊔ zpowers t with hKdef
  have hLK : L ≤ K := le_sup_left
  have hzK : zpowers t ≤ K := le_sup_right
  have hKH : K ≤ H := sup_le hLH hzH
  have hcardK : Nat.card K = Nat.card L * 2 := by
    rw [hKdef, ← Nat.card_congr (mulEquivProdSup (zpowers_le.2 ht) hd).toEquiv,
      Nat.card_prod, Nat.card_zpowers, ht2]
  have hrelK : L.relIndex K = 2 := by
    have h1 := Subgroup.relIndex_mul_card L K
    rw [inf_eq_left.2 hLK, hcardK, Nat.mul_comm (Nat.card L) 2] at h1
    exact Nat.mul_right_cancel Nat.card_pos h1
  have hdvd : K.relIndex H ∣
      (MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)).range.index := by
    rw [hKdef, hHdef]
    exact h.relIndex_sup_zpowers_dvd hS ht ht2
  have hoddw : Odd (K.relIndex H) := hodd.of_dvd_nat hdvd
  have hrelLH : L.relIndex H = 2 * K.relIndex H := by
    rw [← Subgroup.relIndex_mul_relIndex L K H hLK hKH, hrelK]
  let N : Subgroup ↥H := L.subgroupOf H
  have hNnormal : N.Normal := by
    change (L.subgroupOf H).Normal
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).2 hHN
  haveI : N.Normal := hNnormal
  let Q := ↥H ⧸ N
  have hQ_L : Nat.card Q = L.relIndex H := by
    show Nat.card (↥H ⧸ N) = L.relIndex H
    rw [← Subgroup.index_eq_card]
    rfl
  have hQcard : Nat.card Q = 2 * K.relIndex H := by
    rw [hQ_L, hrelLH]
  have hSylow : ∀ P : Sylow 2 Q, Nat.card P = 2 := by
    intro P
    rw [Sylow.card_eq_multiplicity P, hQcard, factorization_two_mul_odd hoddw, pow_one]
  obtain ⟨Bd, hBdN, hBdOdd, hBdIdx⟩ := exists_normal_odd_index_two hSylow
  let M' : Subgroup ↥H := Bd.comap (QuotientGroup.mk' N)
  have hM'idx : M'.index = 2 := by
    rw [Subgroup.index_comap_of_surjective Bd (QuotientGroup.mk'_surjective N)]
    exact hBdIdx
  have hNM' : N ≤ M' := by
    intro x hx
    rw [Subgroup.mem_comap]
    have hx1 : QuotientGroup.mk' N x = 1 := (QuotientGroup.eq_one_iff (N := N) x).2 hx
    rw [hx1]
    exact Bd.one_mem
  have ht'M' : (⟨t, htH⟩ : ↥H) ∉ M' := by
    intro hmem
    have ht'2 : (⟨t, htH⟩ : ↥H) ^ 2 = 1 := by
      have hord : orderOf (⟨t, htH⟩ : ↥H) = 2 := by
        rw [Subgroup.orderOf_mk]
        exact ht2
      rw [← hord]
      exact pow_orderOf_eq_one _
    have hq2 : (QuotientGroup.mk' N (⟨t, htH⟩ : ↥H)) ^ 2 = 1 := by
      rw [← map_pow, ht'2, map_one]
    have hqBd : QuotientGroup.mk' N (⟨t, htH⟩ : ↥H) ∈ Bd := hmem
    have hq1 : QuotientGroup.mk' N (⟨t, htH⟩ : ↥H) = 1 := by
      have hodd_q : Odd (orderOf (QuotientGroup.mk' N (⟨t, htH⟩ : ↥H))) :=
        Odd.of_dvd_nat hBdOdd (Subgroup.orderOf_dvd_natCard Bd hqBd)
      have hdvd2 : orderOf (QuotientGroup.mk' N (⟨t, htH⟩ : ↥H)) ∣ 2 :=
        orderOf_dvd_of_pow_eq_one hq2
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd2 with h1 | h1
      · rwa [orderOf_eq_one_iff] at h1
      · rw [h1] at hodd_q
        norm_num at hodd_q
    have ht'N : (⟨t, htH⟩ : ↥H) ∈ N := (QuotientGroup.eq_one_iff (N := N) _).1 hq1
    have htL' : t ∈ L := by
      rw [Subgroup.mem_subgroupOf] at ht'N
      exact ht'N
    exact htL htL'
  set M : Subgroup G := M'.map H.subtype with hMdef
  have hMH : M ≤ H := Subgroup.map_subtype_le M'
  have hMsub : M.subgroupOf H = M' := by
    rw [hMdef, ← Subgroup.comap_subtype (M'.map H.subtype) H,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective M']
  have hMrelH : M.relIndex H = 2 := by
    show (M.subgroupOf H).index = 2
    rw [hMsub, hM'idx]
  have htM : t ∉ M := by
    intro htM'
    obtain ⟨m, hm, hmeq⟩ := Subgroup.mem_map.1 htM'
    have hmt : m = (⟨t, htH⟩ : ↥H) := Subtype.ext hmeq
    exact ht'M' (hmt ▸ hm)
  have hLM : L ≤ M := by
    intro l hl
    refine Subgroup.mem_map.2 ⟨⟨l, hLH hl⟩, hNM' ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact hl
  have hLMnormal : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).2 (hMH.trans hHN)
  have hLRM : L.relIndex M = K.relIndex H := by
    have h1 := Subgroup.relIndex_mul_relIndex L M H hLM hMH
    rw [hMrelH, hrelLH, ← Nat.mul_comm (K.relIndex H) 2] at h1
    exact Nat.mul_right_cancel (by norm_num) h1
  have hoddLRM : Odd (L.relIndex M) := by
    rw [hLRM]
    exact hoddw
  have hHM : H = M ⊔ zpowers t := by
    apply le_antisymm
    · intro g hg
      by_cases hmem : (⟨g, hg⟩ : ↥H) ∈ M'
      · exact Subgroup.mem_sup_left (Subgroup.mem_map.2 ⟨⟨g, hg⟩, hmem, rfl⟩)
      · have hmul : (⟨g, hg⟩ : ↥H) * ⟨t, htH⟩ ∈ M' := by
          refine (Subgroup.mul_mem_iff_of_index_two hM'idx).2 ?_
          exact ⟨fun h => absurd h hmem, fun h => absurd h ht'M'⟩
        have hgt : g * t ∈ M := Subgroup.mem_map.2 ⟨_, hmul, rfl⟩
        have hg' : g = (g * t) * t⁻¹ := by group
        rw [hg']
        exact mul_mem_sup hgt (Subgroup.inv_mem _ (mem_zpowers t))
    · exact sup_le hMH hzH
  have hMt : Disjoint M (zpowers t) := by
    rw [Subgroup.disjoint_def]
    intro x hxM hxZ
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hxZ
    rw [← hn]
    rw [← hn] at hxM
    have hmod : t ^ n = t ^ (n % (orderOf t : ℤ)) := (zpow_mod_orderOf t n).symm
    have h2 : (orderOf t : ℤ) = 2 := by exact_mod_cast ht2
    rw [h2] at hmod
    rcases Int.emod_two_eq_zero_or_one n with h | h
    · rw [hmod, h]
      simp
    · exfalso
      rw [hmod, h] at hxM
      exact htM (by simpa using hxM)
  refine ⟨M, hLM, hLMnormal, hoddLRM, ?_, hMt⟩
  exact hHM

end CFSG.OddStandard.L2Ree
