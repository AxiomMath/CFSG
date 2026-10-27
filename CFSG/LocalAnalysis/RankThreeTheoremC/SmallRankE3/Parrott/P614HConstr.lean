module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614HRad
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614HLayer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614H

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H S K : Subgroup G} {x z : G}

theorem exists_core33 (hyp : Hyp P M x z H S) (hα : HasPrimeConstraint (G := M) 3) :
    ∃ D E : Subgroup G, M ≤ normalizer (D : Set G) ∧ Nat.Coprime 3 (Nat.card D) ∧
      M ≤ normalizer (E : Set G) ∧ (∀ e ∈ E, ∃ n : ℕ, e ^ 3 ^ n ∈ D) ∧ z ∈ E := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Nb, hNn, hNp, hNc⟩ := hα
  haveI := hNn
  haveI hC : (primeComplementCore (G := M) 3).Normal := primeComplementCore_normal 3
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hyp.setting hyp.situation.mem_sigmaA
    hyp.situation.isCoreMaxLocal
  have hzM : z ∈ M := hPM hyp.central.mem
  haveI : (Nb.comap (QuotientGroup.mk' (primeComplementCore (G := M) 3))).Normal :=
    hNn.comap _
  refine ⟨(primeComplementCore (G := M) 3).map M.subtype,
    (Nb.comap (QuotientGroup.mk' (primeComplementCore (G := M) 3))).map M.subtype,
    le_normalizer_map_subtype _, ?_, le_normalizer_map_subtype _, ?_, ?_⟩
  · rw [card_map_of_injective M.subtype_injective]
    exact primeComplementCore_coprime 3
  · rintro _ ⟨m, hm, rfl⟩
    obtain ⟨n, hn⟩ := hNp ⟨QuotientGroup.mk' _ m, hm⟩
    refine ⟨n, ⟨m ^ 3 ^ n, ?_, rfl⟩⟩
    have h1 : QuotientGroup.mk' (primeComplementCore (G := M) 3) (m ^ 3 ^ n) = 1 := by
      rw [map_pow]
      simpa using congrArg Subtype.val hn
    exact (QuotientGroup.eq_one_iff _).mp h1
  · refine ⟨⟨z, hzM⟩, ?_, rfl⟩
    show QuotientGroup.mk' _ ⟨z, hzM⟩ ∈ Nb
    apply hNc
    rw [mem_centralizer_iff]
    intro n hn
    let Pbar : Sylow 3 (M ⧸ primeComplementCore (G := M) 3) :=
      (P.subtype hPM).mapSurjective (QuotientGroup.mk'_surjective _)
    have hnP : n ∈ (Pbar : Subgroup (M ⧸ primeComplementCore (G := M) 3)) :=
      hNp.le_sylow_of_normal Pbar hn
    obtain ⟨p, hp, rfl⟩ := hnP
    have hp' : (p : G) ∈ (P : Subgroup G) := hp
    have hpz : (p : G) * z = z * p := mem_centralizer_iff.mp hyp.central.centralizes p hp'
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hpz

theorem mk_mem_normalizer_bar {A : Subgroup G} {k : K} (hk : (k : G) ∈ normalizer (A : Set G)) :
    kbarMk K k ∈ normalizer (bar K A : Set (Kbar K)) :=
  le_normalizer_map (kbarMk K) ⟨k, le_normalizer_comap K.subtype hk, rfl⟩

theorem bar_kPar_le_normalizer (hL : LieCase M H S K x z) {A : Subgroup G}
    (hMA : M ≤ normalizer (A : Set G)) :
    bar K (kPar H S K) ≤ normalizer (bar K (A ⊓ kPar H S K) : Set (Kbar K)) := by
  rintro _ ⟨k, hk, rfl⟩
  have hk' : (k : G) ∈ kPar H S K := hk
  exact mk_mem_normalizer_bar
    (inf_normalizer_le_normalizer_inf ⟨hMA (hL.par_le hk'), le_normalizer hk'⟩)

theorem bar_inf_kPar_le (hyp : Hyp P M x z H S) (h618 : Stage618 M H K z) (A : Subgroup G) :
    bar K (A ⊓ kPar H S K) ≤ normalizer (bar K (kRad H S K) : Set (Kbar K)) := by
  rintro _ ⟨k, hk, rfl⟩
  exact (mk_mem_normalizer_bar_kRad_iff hyp h618 k).2 (mem_inf.mp hk).2

theorem card_bar_dvd (A : Subgroup G) : Nat.card (bar K A) ∣ Nat.card A := by
  refine (card_map_dvd _ _).trans ?_
  rw [← card_map_of_injective K.subtype_injective, subgroupOf_map_subtype]
  exact card_dvd_of_le inf_le_left

theorem pLayer_normalizer_bar_kRad_eq_bot (hyp : Hyp P M x z H S) (h618 : Stage618 M H K z)
    (hL : LieCase M H S K x z) :
    CFSG.pLayer (normalizer (bar K (kRad H S K) : Set (Kbar K))) 3 = ⊥ := by
  obtain ⟨D, E, hMD, hD, hME, hDE, hzE⟩ := exists_core33 hyp h618.alpha
  have hN := normalizer_bar_kRad hyp h618
  have hDN := bar_inf_kPar_le hyp h618 D
  have hEN := bar_inf_kPar_le hyp h618 E
  haveI hDn : ((bar K (D ⊓ kPar H S K)).subgroupOf
      (normalizer (bar K (kRad H S K) : Set (Kbar K)))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hDN).2 (hN ▸ bar_kPar_le_normalizer hL hMD)
  haveI hEn : ((bar K (E ⊓ kPar H S K)).subgroupOf
      (normalizer (bar K (kRad H S K) : Set (Kbar K)))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hEN).2 (hN ▸ bar_kPar_le_normalizer hL hME)
  have hzK := z_mem h618
  have hzP : z ∈ kPar H S K := hL.par_mem (mem_zpowers z)
  have hzN : zbar h618 ∈ normalizer (bar K (kRad H S K) : Set (Kbar K)) :=
    (mk_mem_normalizer_bar_kRad_iff hyp h618 ⟨z, hzK⟩).2 hzP
  refine pLayer_eq_bot (D := (bar K (D ⊓ kPar H S K)).subgroupOf _)
    (E := (bar K (E ⊓ kPar H S K)).subgroupOf _) (w := ⟨zbar h618, hzN⟩) ?_ ?_ ?_ ?_ ?_
  · rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact (CFSG.SectionRank.pRank_mono (by norm_num) le_top).trans (pRank_kbar h618).le
  · rw [Nat.card_congr (subgroupOfEquivOfLe hDN).toEquiv]
    exact Nat.Coprime.coprime_dvd_right
      ((card_bar_dvd _).trans (card_dvd_of_le inf_le_left)) hD
  · intro e he
    rw [mem_subgroupOf] at he
    obtain ⟨e', he', hee'⟩ := he
    have he'' : (e' : G) ∈ E ⊓ kPar H S K := he'
    obtain ⟨n, hn⟩ := hDE _ (mem_inf.mp he'').1
    refine ⟨n, ?_⟩
    rw [mem_subgroupOf, SubgroupClass.coe_pow, ← hee', ← map_pow]
    refine ⟨e' ^ 3 ^ n, ?_, rfl⟩
    show ((e' ^ 3 ^ n : K) : G) ∈ D ⊓ kPar H S K
    rw [SubgroupClass.coe_pow]
    exact mem_inf.mpr ⟨hn, pow_mem (mem_inf.mp he'').2 _⟩
  · rw [mem_subgroupOf]
    exact ⟨⟨z, hzK⟩, mem_inf.mpr ⟨hzE, hzP⟩, rfl⟩
  · rw [Subgroup.orderOf_mk]
    exact orderOf_zbar hyp h618

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614H
