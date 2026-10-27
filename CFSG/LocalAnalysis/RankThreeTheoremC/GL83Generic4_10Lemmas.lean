module

import CFSG.LocalAnalysis.PreuniquenessRankFour.Nongeneration
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup
open scoped commutatorElement

theorem u3main_center_bot {G : Type} [Group G] {J O : Subgroup G} (hOJ : O ≤ J)
    (hperf : Group.IsPerfect J) (hlt : O < J)
    (hmin : ∀ N : Subgroup G, N ≤ J → (N.subgroupOf J).Normal → O ≤ N → N = O ∨ N = J)
    {Q : Type} [Group Q] (ψ : ↥J →* Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = O.subgroupOf J) : center Q = ⊥ := by
  have hkerne : ψ.ker ≠ ⊤ := by
    intro h
    rw [hker, subgroupOf_eq_top] at h
    exact hlt.ne (le_antisymm hOJ h)
  have hQsimple : IsSimpleGroup Q := by
    refine { toNontrivial := ?_, eq_bot_or_eq_top_of_normal := ?_ }
    · by_contra hcon
      rw [not_nontrivial_iff_subsingleton] at hcon
      exact hkerne (eq_top_iff.mpr fun j _ => Subsingleton.elim _ _)
    · intro S hS
      set N : Subgroup G := (S.comap ψ).map J.subtype with hN
      have hNJ : N ≤ J := map_subtype_le _
      have hNsub : N.subgroupOf J = S.comap ψ :=
        comap_map_eq_self_of_injective J.subtype_injective _
      have hNn : (N.subgroupOf J).Normal := by
        rw [hNsub]
        exact Normal.comap hS ψ
      have hON : O ≤ N := by
        intro o ho
        refine ⟨⟨o, hOJ ho⟩, ?_, rfl⟩
        show ψ ⟨o, hOJ ho⟩ ∈ S
        have : (⟨o, hOJ ho⟩ : J) ∈ ψ.ker := by
          rw [hker, mem_subgroupOf]
          exact ho
        rw [MonoidHom.mem_ker.mp this]
        exact S.one_mem
      rcases hmin N hNJ hNn hON with h | h
      · left
        rw [eq_bot_iff]
        intro s hs
        obtain ⟨j, rfl⟩ := hψ s
        have hj : j ∈ S.comap ψ := hs
        rw [← hNsub, h, ← hker] at hj
        exact MonoidHom.mem_ker.mp hj
      · right
        rw [eq_top_iff]
        intro s _
        obtain ⟨j, rfl⟩ := hψ s
        have : j ∈ N.subgroupOf J := by
          rw [h, subgroupOf_self]
          exact mem_top j
        rw [hNsub] at this
        exact this
  rcases hQsimple.eq_bot_or_eq_top_of_normal (center Q) with h | h
  · exact h
  · exfalso
    apply hkerne
    rw [eq_top_iff, ← (Group.isPerfect_def).mp hperf]
    refine commutator_le.mpr fun g₁ _ g₂ _ => ?_
    have h1 : ψ g₁ ∈ center Q := h ▸ mem_top _
    have hc : ⁅ψ g₁, ψ g₂⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp h1 (ψ g₂)).symm
    rw [MonoidHom.mem_ker, map_commutatorElement, hc]

theorem u3main_not_mem {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {J O : Subgroup G} {x : G} (hx1 : x ≠ 1) (hxp : x ^ p = 1)
    (hJC : J ≤ centralizer ({x} : Set G)) (hcop : ¬ p ∣ Nat.card O) {Q : Type} [Group Q]
    (ψ : ↥J →* Q) (hψ : Function.Surjective ψ) (hker : ψ.ker = O.subgroupOf J)
    (hZ : center Q = ⊥) : x ∉ J := by
  intro hxJ
  have hc : ψ ⟨x, hxJ⟩ ∈ center Q := by
    rw [mem_center_iff]
    intro q
    obtain ⟨j, rfl⟩ := hψ q
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext (mem_centralizer_singleton_iff.mp (hJC j.2)))
  rw [hZ, mem_bot] at hc
  have hmem : (⟨x, hxJ⟩ : J) ∈ ψ.ker := hc
  rw [hker, mem_subgroupOf] at hmem
  have hord : orderOf (⟨x, hmem⟩ : O) = p := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hxp hx1
  exact hcop (hord ▸ orderOf_dvd_natCard _)

theorem u3main_eq_one_of_ker {J K : Type} [Group J] [Group K] {p : ℕ} [Fact p.Prime]
    (ψ : J →* K) (hcop : ¬ p ∣ Nat.card ψ.ker) {T : Subgroup J} (hT : IsPGroup p T) :
    ∀ t ∈ T, ψ t = 1 → t = 1 := by
  intro t ht h1
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hT ⟨t, ht⟩
  have hord : orderOf t = p ^ k := by rw [← hk, Subgroup.orderOf_mk]
  have hdvd : orderOf t ∣ Nat.card ψ.ker := by
    have : orderOf (⟨t, MonoidHom.mem_ker.mpr h1⟩ : ψ.ker) ∣ Nat.card ψ.ker :=
      orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk] at this
  have hcop' : Nat.Coprime (p ^ k) (Nat.card ψ.ker) :=
    ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hcop).pow_left k
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (hord ▸ hcop') hdvd)

theorem u3main_exists_central_lift {J K : Type} [Group J] [Group K] {p : ℕ} (ψ : J →* K)
    {T : Subgroup J} (hinj : ∀ t ∈ T, ψ t = 1 → t = 1) {u : K} (hu : u ∈ T.map ψ)
    (hup : u ^ p = 1) (huc : ∀ w ∈ T.map ψ, w * u = u * w) :
    ∃ c ∈ T, ψ c = u ∧ c ^ p = 1 ∧ ∀ t ∈ T, c * t = t * c := by
  obtain ⟨c, hcT, rfl⟩ := hu
  refine ⟨c, hcT, rfl, hinj _ (T.pow_mem hcT p) (by rw [map_pow, hup]), fun t ht => ?_⟩
  have h1 : ⁅c, t⁆ ∈ T := T.mul_mem (T.mul_mem (T.mul_mem hcT ht) (T.inv_mem hcT)) (T.inv_mem ht)
  have h2 : ⁅c, t⁆ = 1 := hinj _ h1 (by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (huc (ψ t) (mem_map_of_mem ψ ht)).symm)
  exact commutatorElement_eq_one_iff_mul_comm.mp h2

theorem u3main_pRank_map {J K : Type} [Group J] [Finite J] [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (ψ : J →* K) {T : Subgroup J} (hinj : ∀ t ∈ T, ψ t = 1 → t = 1) :
    CFSG.Open.pRank p (T.map ψ) = CFSG.Open.pRank p T := by
  have hf : Function.Injective (ψ.comp T.subtype) :=
    (injective_iff_map_eq_one _).mpr fun a ha => Subtype.ext (hinj a a.2 ha)
  have e1 : (⊤ : Subgroup ↥T).map T.subtype = T := by rw [Subgroup.map_top, range_subtype]
  have e2 : (⊤ : Subgroup ↥T).map (ψ.comp T.subtype) = T.map ψ := by rw [← map_map, e1]
  have h1 := CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp _ hf ⊤
  have h2 := CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp _ T.subtype_injective ⊤
  rw [e2] at h1
  rw [e1] at h2
  rw [h1, h2]

theorem u3main_mem_normalizer_map {G : Type} [Group G] {J : Subgroup G} {T : Subgroup ↥J}
    {g : ↥J} (hg : g ∈ normalizer (T : Set ↥J)) :
    (g : G) ∈ normalizer ((T.map J.subtype : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hg ⊢
  intro h
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨g * t * g⁻¹, (hg t).mp ht, rfl⟩
  · rintro ⟨t', ht', hh⟩
    refine ⟨g⁻¹ * t' * g, ?_, ?_⟩
    · exact (hg (g⁻¹ * t' * g)).mpr (by simpa [mul_assoc] using ht')
    · show ((g⁻¹ * t' * g : ↥J) : G) = h
      have h1 : (t' : G) = (g : G) * h * (g : G)⁻¹ := hh
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, h1]
      group

end CFSG.LocalAnalysis.RankThreeTheoremC
