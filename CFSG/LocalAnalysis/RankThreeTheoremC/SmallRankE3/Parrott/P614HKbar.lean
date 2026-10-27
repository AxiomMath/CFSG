module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614HBasic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614H

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H S K : Subgroup G} {x z : G}

theorem orderOf_z (hyp : Hyp P M x z H S) : orderOf z = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime hyp.central.pow_eq_one hyp.central.ne_one

theorem S_le (hyp : Hyp P M x z H S) : S ≤ H :=
  hyp.optimal.maxInv.1.1

theorem sup_le_normalizer (hyp : Hyp P M x z H S) (h618 : Stage618 M H K z) :
    K ⊔ S ≤ normalizer (K : Set G) :=
  sup_le le_normalizer ((S_le hyp).trans h618.comp.normal)

theorem z_mem (h618 : Stage618 M H K z) : z ∈ K :=
  h618.comp.mem (mem_zpowers z)

theorem normal_pCoreOf_subgroupOf (h618 : Stage618 M H K z) :
    ((pCoreOf 2 H).subgroupOf K).Normal := by
  constructor
  intro n hn g
  rw [mem_subgroupOf] at hn ⊢
  have h := (mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (h618.comp.le g.2)) n).mp hn
  simpa using h

theorem isPGroup_pCoreOf_subgroupOf (K H : Subgroup G) :
    IsPGroup 2 ((pCoreOf 2 H).subgroupOf K) :=
  (isPGroup_pCoreOf 2 H).comap_subtype

theorem not_mem_pCoreOf_of_orderOf {g : G} (hg : orderOf g = 3) : g ∉ pCoreOf 2 H := by
  intro h
  obtain ⟨n, hn⟩ := isPGroup_pCoreOf 2 H ⟨g, h⟩
  have h1 : orderOf g ∣ 2 ^ n :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hn)
  rw [hg] at h1
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1) (by norm_num)

theorem mem_pPrimeCore_iff (hyp : Hyp P M x z H S) (h618 : Stage618 M H K z) (k : K) :
    k ∈ CFSG.pPrimeCore 3 K ↔ (k : G) ∈ pCoreOf 2 H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : (pCoreOf 2 H).subgroupOf K ≤ CFSG.pPrimeCore 3 K :=
    le_sSup (s := {N : Subgroup K | N.Normal ∧ Nat.Coprime 3 (Nat.card N)})
      ⟨normal_pCoreOf_subgroupOf h618,
        coprime_three_of_isPGroup_two (isPGroup_pCoreOf_subgroupOf K H)⟩
  refine ⟨fun hk => ?_, fun hk => hle hk⟩
  have hNsub : ((CFSG.pPrimeCore 3 K).map K.subtype).subgroupOf K = CFSG.pPrimeCore 3 K :=
    comap_map_eq_self_of_injective K.subtype_injective _
  have hNn : (((CFSG.pPrimeCore 3 K).map K.subtype).subgroupOf K).Normal := by
    rw [hNsub]
    exact CFSG.pPrimeCore_normal
  have hON : K ⊓ rankThreePrimeCore 3 H ≤ (CFSG.pPrimeCore 3 K).map K.subtype := by
    rw [h618.core_eq]
    intro y hy
    exact ⟨⟨y, hy.1⟩, hle (by rw [mem_subgroupOf]; exact hy.2), rfl⟩
  rcases h618.comp.maximal _ (map_subtype_le _) hNn hON with h | h
  · have hk' : (k : G) ∈ (CFSG.pPrimeCore 3 K).map K.subtype := ⟨k, hk, rfl⟩
    rw [h, h618.core_eq] at hk'
    exact hk'.2
  · exfalso
    have hzK : z ∈ K := z_mem h618
    have hzN : (⟨z, hzK⟩ : K) ∈ CFSG.pPrimeCore 3 K := by
      rw [← hNsub, h, mem_subgroupOf]
      exact hzK
    have h3 : 3 ∣ Nat.card (CFSG.pPrimeCore 3 K) := by
      have := Subgroup.orderOf_dvd_natCard _ hzN
      rwa [Subgroup.orderOf_mk, orderOf_z hyp] at this
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := K)) h3

abbrev kbarMk (K : Subgroup G) : K →* Kbar K :=
  QuotientGroup.mk' (CFSG.pPrimeCore 3 K)

theorem kbarMk_eq_one_iff (hyp : Hyp P M x z H S) (h618 : Stage618 M H K z) (k : K) :
    kbarMk K k = 1 ↔ (k : G) ∈ pCoreOf 2 H := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_pPrimeCore_iff hyp h618]

theorem exists_not_mem_pCoreOf (h618 : Stage618 M H K z) : ∃ k ∈ K, k ∉ pCoreOf 2 H := by
  by_contra hcon
  push Not at hcon
  apply h618.comp.lt.not_ge
  intro y hy
  exact ⟨hy, h618.core_eq ▸ hcon y hy⟩

theorem isSimpleGroup_kbar (hyp : Hyp P M x z H S) (h618 : Stage618 M H K z) :
    IsSimpleGroup (Kbar K) := by
  obtain ⟨k₀, hk₀K, hk₀O⟩ := exists_not_mem_pCoreOf h618
  have hne : kbarMk K ⟨k₀, hk₀K⟩ ≠ 1 := fun h => hk₀O ((kbarMk_eq_one_iff hyp h618 _).1 h)
  refine
    { exists_pair_ne := ⟨_, _, hne⟩
      eq_bot_or_eq_top_of_normal := fun N hN => ?_ }
  have hNsub : ((N.comap (kbarMk K)).map K.subtype).subgroupOf K = N.comap (kbarMk K) :=
    comap_map_eq_self_of_injective K.subtype_injective _
  have hNn : (((N.comap (kbarMk K)).map K.subtype).subgroupOf K).Normal := by
    rw [hNsub]
    exact hN.comap _
  have hON : K ⊓ rankThreePrimeCore 3 H ≤ (N.comap (kbarMk K)).map K.subtype := by
    rw [h618.core_eq]
    intro y hy
    rw [mem_inf] at hy
    refine ⟨⟨y, hy.1⟩, ?_, rfl⟩
    show kbarMk K ⟨y, hy.1⟩ ∈ N
    rw [(kbarMk_eq_one_iff hyp h618 _).2 hy.2]
    exact N.one_mem
  rcases h618.comp.maximal _ (map_subtype_le _) hNn hON with h | h
  · left
    rw [eq_bot_iff]
    intro n hn
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective _ n
    have hk : (k : G) ∈ (N.comap (kbarMk K)).map K.subtype := ⟨k, hn, rfl⟩
    rw [h, h618.core_eq] at hk
    exact (kbarMk_eq_one_iff hyp h618 k).2 hk.2
  · right
    rw [eq_top_iff]
    intro n _
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective _ n
    have hk : k ∈ ((N.comap (kbarMk K)).map K.subtype).subgroupOf K := by
      rw [h, mem_subgroupOf]
      exact k.2
    rw [hNsub] at hk
    exact hk

theorem commutator_K_eq_top (h618 : Stage618 M H K z) : commutator K = ⊤ := by
  apply map_injective K.subtype_injective
  rw [map_subtype_commutator, h618.comp.perfect, ← MonoidHom.range_eq_map, range_subtype]

theorem commutator_kbar_eq_top (h618 : Stage618 M H K z) : commutator (Kbar K) = ⊤ := by
  have hs := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 K)
  rw [commutator_def, ← map_top_of_surjective _ hs, ← map_commutator, ← commutator_def,
    commutator_K_eq_top h618]

theorem exists_ne_comm_kbar (hyp : Hyp P M x z H S) (h618 : Stage618 M H K z) :
    ∃ a b : Kbar K, a * b ≠ b * a := by
  haveI := (isSimpleGroup_kbar hyp h618).toNontrivial
  by_contra h
  push Not at h
  have : IsMulCommutative (Kbar K) := ⟨⟨h⟩⟩
  have h1 := Abelianization.commutator_subset_ker (MonoidHom.id (Kbar K))
  rw [commutator_kbar_eq_top h618, MonoidHom.ker_id, top_le_iff] at h1
  exact bot_ne_top h1

theorem isKGroup_kbar (hyp : Hyp P M x z H S) (h618 : Stage618 M H K z) :
    CFSG.IsKGroup (Kbar K) := by
  haveI : IsSimpleGroup G := hyp.setting.simple
  have hH : CFSG.IsKGroup H :=
    CFSG.ComponentClassification.CatalogueKProper.proper_subgroup_isKGroup
      (CFSG.ComponentClassification.CatalogueKProper.open_isKProper_iff.1 hyp.setting.kProper)
      H (twoLocal_ne_top hyp.setting.nonab H hyp.optimal.ext.pair.isTwoLocal)
  exact (hH.of_injective (inclusion h618.comp.le) (inclusion_injective _)).quotient _

theorem pRank_kbar (h618 : Stage618 M H K z) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (Kbar K)) = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [CFSG.SectionRank.pRank_quotient_eq _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := K))),
    ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup K]
  exact h618.comp.rank_one

abbrev zbar (h618 : Stage618 M H K z) : Kbar K :=
  kbarMk K ⟨z, z_mem h618⟩

theorem orderOf_zbar (hyp : Hyp P M x z H S) (h618 : Stage618 M H K z) :
    orderOf (zbar h618) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply orderOf_eq_prime
  · rw [← map_pow, show (⟨z, z_mem h618⟩ : K) ^ 3 = 1 from
      Subtype.ext (by simpa using hyp.central.pow_eq_one), map_one]
  · intro h
    rw [kbarMk_eq_one_iff hyp h618] at h
    exact not_mem_pCoreOf_of_orderOf (orderOf_z hyp) h

noncomputable def kbarEquiv (hyp : Hyp P M x z H S) (h618 : Stage618 M H K z) {T : Type*}
    [Group T] (f : K →* T) (hf : Function.Surjective f)
    (hker : ∀ k : K, f k = 1 ↔ (k : G) ∈ pCoreOf 2 H) : Kbar K ≃* T :=
  (QuotientGroup.quotientMulEquivOfEq (by
      ext k
      rw [mem_pPrimeCore_iff hyp h618, MonoidHom.mem_ker, hker])).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

theorem card_kbar_eq (hyp : Hyp P M x z H S) (h618 : Stage618 M H K z) {T : Type*}
    [Group T] (f : K →* T) (hf : Function.Surjective f)
    (hker : ∀ k : K, f k = 1 ↔ (k : G) ∈ pCoreOf 2 H) : Nat.card (Kbar K) = Nat.card T :=
  Nat.card_congr (kbarEquiv hyp h618 f hf hker).toEquiv

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614H
