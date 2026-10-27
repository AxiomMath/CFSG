module

import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511A
import TauCeti.Algebra.Group.Coprime
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Vocab

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.ABGLocalTools Subgroup

section Helpers

private theorem kSecLift_isSylowOf_map {X Y : Type*} [Group X] [Finite X] [Group Y] {p : ℕ} [Fact p.Prime]
    {P K : Subgroup X} (h : IsSylowOf p P K) (f : X →* Y) : IsSylowOf p (P.map f) (K.map f) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (f.subgroupMap_surjective K), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

private theorem kSecLift_exists_pElement {X Y : Type*} [Group X] [Finite X] [Group Y] {p : ℕ} (hp : p.Prime)
    (f : X →* Y) {S : Subgroup X} {a : Y} (ha : a ∈ S.map f) (hap : ∃ k : ℕ, a ^ p ^ k = 1) :
    ∃ n ∈ S, (∃ k : ℕ, n ^ p ^ k = 1) ∧ f n = a := by
  obtain ⟨n₀, hn₀, rfl⟩ := ha
  obtain ⟨k, hk⟩ := hap
  obtain ⟨s, u, hu, hsu⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos n₀).ne' p hp.ne_one
  have hcop : Nat.Coprime u (p ^ k) :=
    (Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hp).2 hu).symm)
  have hmod : u ^ Nat.totient (p ^ k) % p ^ k = 1 % p ^ k := Nat.ModEq.pow_totient hcop
  have htot : Nat.totient (p ^ k) ≠ 0 := (Nat.totient_pos.2 (pow_pos hp.pos k)).ne'
  refine ⟨n₀ ^ u ^ Nat.totient (p ^ k), S.pow_mem hn₀ _, ⟨s, ?_⟩, ?_⟩
  · rw [← pow_mul]
    refine orderOf_dvd_iff_pow_eq_one.1 ?_
    rw [hsu, mul_comm]
    exact mul_dvd_mul_right (dvd_pow_self u htot) _
  · rw [map_pow, pow_eq_pow_mod _ hk, hmod, ← pow_eq_pow_mod _ hk, pow_one]

private theorem kSecLift_isPGroup_zpowers {G : Type*} [Group G] {p k : ℕ} {t : G} (ht : t ^ p ^ k = 1) :
    IsPGroup p (Subgroup.zpowers t) := by
  rintro ⟨s, hs⟩
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
  refine ⟨k, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht, one_zpow]

private theorem kSecLift_exists_conj_mem {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {D S : Subgroup G} (hS : IsSylowOf p S D) {a : G} (haD : a ∈ D) (ha : ∃ k : ℕ, a ^ p ^ k = 1) :
    ∃ d ∈ D, d * a * d⁻¹ ∈ S := by
  obtain ⟨Q, hQ⟩ := hS.exists_sylow_eq_subgroupOf
  obtain ⟨k, hk⟩ := ha
  have hk' : (⟨a, haD⟩ : D) ^ p ^ k = 1 := Subtype.ext (by simpa using hk)
  obtain ⟨R, hR⟩ := (kSecLift_isPGroup_zpowers hk').exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq D Q R
  have hxR : (⟨a, haD⟩ : D) ∈ (R : Subgroup D) := hR (Subgroup.mem_zpowers _)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxR
  have h1 : (MulAut.conj g)⁻¹ • (⟨a, haD⟩ : D) = g⁻¹ * ⟨a, haD⟩ * g := by simp [MulAut.smul_def]
  rw [h1, hQ] at hxR
  refine ⟨((g⁻¹ : D) : G), (g⁻¹ : D).2, ?_⟩
  have h2 : (((g⁻¹ * ⟨a, haD⟩ * g : D)) : G) ∈ S := hxR
  simpa using h2

private theorem kSecLift_top_le_normalizer {G : Type*} [Group G] (N : Subgroup G) [N.Normal] :
    (⊤ : Subgroup G) ≤ Subgroup.normalizer (N : Set G) := fun g _ =>
  Subgroup.mem_normalizer_iff.2 fun h =>
    ⟨fun hh => Subgroup.Normal.conj_mem inferInstance h hh g, fun hh => by
      simpa [mul_assoc] using Subgroup.Normal.conj_mem inferInstance _ hh g⁻¹⟩

private theorem kSecLift_mem_of_pElement {G : Type*} [Group G] {L H : Subgroup G} (hLH : L ≤ H) [L.Normal]
    {r : ℕ} (hr : r.Prime) (hcop : ¬ r ∣ L.relIndex H) {n : G} (hn : n ∈ H)
    (hrn : ∃ k : ℕ, n ^ r ^ k = 1) : n ∈ L := by
  obtain ⟨k, hk⟩ := hrn
  haveI : (L.subgroupOf H).Normal := Subgroup.Normal.subgroupOf inferInstance H
  have h1 : (⟨n, hn⟩ : H) ^ r ^ k ∈ L.subgroupOf H := by
    have : (⟨n, hn⟩ : H) ^ r ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [this]
    exact one_mem _
  have h2 : (⟨n, hn⟩ : H) ^ (L.subgroupOf H).index ∈ L.subgroupOf H := Subgroup.pow_index_mem _ _
  have hc : Nat.Coprime (r ^ k) (L.subgroupOf H).index :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hr).2 hcop)
  obtain ⟨i, j, hij⟩ := TauCeti.exists_zpow_mul_zpow_eq_of_coprime (G := H) hc
  have h3 := hij ⟨n, hn⟩
  have h4 : (⟨n, hn⟩ : H) ∈ L.subgroupOf H := by
    rw [← h3]
    exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ h1 i) (Subgroup.zpow_mem _ h2 j)
  exact h4

end Helpers

section KSecLiftParts

variable {X : Type} [Group X] [Finite X]

theorem gnA_two_element_mem_map_normalizer_two {T T₁ T₂ : Subgroup X} (hX : GNSetting X T)
    (hg : GNGood T T₁ T₂) {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hL : LiftOf T L Ls)
    (hLn : L.Normal) {a : X ⧸ gnC T} (ha : a ∈ gnA T T₂ Ls) (h2 : ∃ k : ℕ, a ^ 2 ^ k = 1) :
    a ∈ (Subgroup.normalizer (T₂ : Set X) ⊓ L).map (toStar T) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hHn : (L ⊔ gnC T).Normal := inferInstance
  have hmapH : (L ⊔ gnC T).map (toStar T) = L.map (toStar T) := by
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
  have hD : a ∈ (Subgroup.normalizer (T₂ : Set X) ⊓ (L ⊔ gnC T)).map (toStar T) := by
    obtain ⟨⟨n, hn, rfl⟩, haL⟩ := ha
    refine ⟨n, ⟨hn, ?_⟩, rfl⟩
    have h1 : n ∈ Ls.comap (toStar T) := haL
    rwa [← hL.2, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h1
  obtain ⟨n, hnD, hnk, rfl⟩ := kSecLift_exists_pElement Nat.prime_two (toStar T) hD h2
  have hTT : IsSylowOf 2 T ⊤ := isSylowOf_iff.2 ⟨hX.sylow.1, hX.sylow.2.1, hX.sylow.2.2⟩
  have hTH : IsSylowOf 2 (T ⊓ (L ⊔ gnC T)) (L ⊔ gnC T) :=
    hTT.inf_of_le_normalizer le_top (kSecLift_top_le_normalizer _)
  have hTN : T ≤ Subgroup.normalizer (T₂ : Set X) := IsGNPair.le_normalizer₂ hg.pair
  have hSD : IsSylowOf 2 (T ⊓ (L ⊔ gnC T)) (Subgroup.normalizer (T₂ : Set X) ⊓ (L ⊔ gnC T)) :=
    hTH.of_le (inf_le_inf_right _ hTN) inf_le_right
  obtain ⟨d, hd, hdS⟩ := kSecLift_exists_conj_mem hSD hnD hnk
  have hTL : IsSylowOf 2 (T ⊓ L) L := hTT.inf_of_le_normalizer le_top (kSecLift_top_le_normalizer _)
  have hTLs : IsSylowOf 2 ((T ⊓ L).map (toStar T)) (L.map (toStar T)) :=
    kSecLift_isSylowOf_map hTL (toStar T)
  have hEq : (T ⊓ (L ⊔ gnC T)).map (toStar T) = (T ⊓ L).map (toStar T) :=
    hTLs.eq_of_le (Subgroup.map_mono (inf_le_inf_left T le_sup_left))
      ((Subgroup.map_mono inf_le_right).trans hmapH.le)
      (hX.sylow.2.1.to_inf_left.map (toStar T))
  have hmem : toStar T (d * n * d⁻¹) ∈ (T ⊓ L).map (toStar T) := hEq ▸ ⟨_, hdS, rfl⟩
  obtain ⟨t, ht, hφt⟩ := hmem
  refine ⟨d⁻¹ * t * d, ⟨?_, ?_⟩, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hd.1) (hTN ht.1)) hd.1
  · simpa using hLn.conj_mem t ht.2 d⁻¹
  · rw [map_mul, map_mul, map_inv, hφt, map_mul, map_mul, map_inv]
    group

theorem gnA_pElement_mem_map_normalizer_two_of_not_dvd {T T₂ : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    {L : Subgroup X} (hL : LiftOf T L Ls) (hLn : L.Normal) {r : ℕ} (hr : r.Prime)
    (hcop : ¬ r ∣ (L ⊓ gnC T).relIndex (gnC T)) {a : X ⧸ gnC T} (ha : a ∈ gnA T T₂ Ls)
    (hra : ∃ k : ℕ, a ^ r ^ k = 1) :
    a ∈ (Subgroup.normalizer (T₂ : Set X) ⊓ L).map (toStar T) := by
  haveI := hLn
  have hD : a ∈ (Subgroup.normalizer (T₂ : Set X) ⊓ (L ⊔ gnC T)).map (toStar T) := by
    obtain ⟨⟨n, hn, rfl⟩, haL⟩ := ha
    refine ⟨n, ⟨hn, ?_⟩, rfl⟩
    have h1 : n ∈ Ls.comap (toStar T) := haL
    rwa [← hL.2, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h1
  obtain ⟨n, hnD, hnk, rfl⟩ := kSecLift_exists_pElement hr (toStar T) hD hra
  have hidx : L.relIndex (L ⊔ gnC T) = (L ⊓ gnC T).relIndex (gnC T) := by
    rw [Subgroup.inf_relIndex_right, sup_comm]
    exact relIndex_sup_eq_relIndex_of_normal (gnC T) L
  have hnL : n ∈ L :=
    kSecLift_mem_of_pElement le_sup_left hr (by rwa [hidx]) hnD.2 hnk
  exact ⟨n, ⟨hnD.1, hnL⟩, rfl⟩

theorem gnA_le_map_normalizer_two_of_odd_primes {T T₁ T₂ : Subgroup X} (hX : GNSetting X T)
    (hg : GNGood T T₁ T₂) {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hL : LiftOf T L Ls)
    (hLn : L.Normal)
    (hodd : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ (L ⊓ gnC T).relIndex (gnC T) →
      ∀ a ∈ gnA T T₂ Ls, (∃ k : ℕ, a ^ r ^ k = 1) →
        a ∈ (Subgroup.normalizer (T₂ : Set X) ⊓ L).map (toStar T)) :
    gnA T T₂ Ls ≤ (Subgroup.normalizer (T₂ : Set X) ⊓ L).map (toStar T) := by
  intro a ha
  refine Subgroup.mem_of_forall_prime_exists_pow_mem fun r hr => ?_
  have ho : 0 < orderOf a := orderOf_pos a
  refine ⟨ordCompl[r] (orderOf a), Nat.not_dvd_ordCompl hr ho.ne', ?_⟩
  have hpa : a ^ ordCompl[r] (orderOf a) ∈ gnA T T₂ Ls := Subgroup.pow_mem _ ha _
  have hpk : ∃ k : ℕ, (a ^ ordCompl[r] (orderOf a)) ^ r ^ k = 1 := by
    refine ⟨(orderOf a).factorization r, ?_⟩
    rw [← pow_mul, mul_comm, Nat.ordProj_mul_ordCompl_eq_self]
    exact pow_orderOf_eq_one a
  by_cases h2 : r = 2
  · subst h2
    exact gnA_two_element_mem_map_normalizer_two hX hg hL hLn hpa hpk
  · by_cases hdv : r ∣ (L ⊓ gnC T).relIndex (gnC T)
    · exact hodd r hr h2 hdv _ hpa hpk
    · exact gnA_pElement_mem_map_normalizer_two_of_not_dvd hL hLn hr hdv hpa hpk

theorem gnA_le_map_normalizer_two_of_relIndex_two_pow {T T₁ T₂ : Subgroup X} (hX : GNSetting X T)
    (hg : GNGood T T₁ T₂) {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hL : LiftOf T L Ls)
    (hLn : L.Normal) (hpow : ∃ k : ℕ, (L ⊓ gnC T).relIndex (gnC T) = 2 ^ k) :
    gnA T T₂ Ls ≤ (Subgroup.normalizer (T₂ : Set X) ⊓ L).map (toStar T) := by
  refine gnA_le_map_normalizer_two_of_odd_primes hX hg hL hLn fun r hr hr2 hdv => ?_
  obtain ⟨k, hk⟩ := hpow
  rw [hk] at hdv
  exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow hdv)) hr2

end KSecLiftParts

end CFSG.LocalAnalysis.RankThreeUC.S15
