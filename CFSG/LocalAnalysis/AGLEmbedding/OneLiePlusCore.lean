module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section PlusCore

variable {G : Type} [Group G] [Finite G]

theorem coprime_card_map_comap_mk {p : ℕ} (H : Subgroup G)
    {W : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hW : p.Coprime (Nat.card W)) :
    p.Coprime (Nat.card ((W.comap (QuotientGroup.mk' (primeComplementCore (G := H) p))).map
      H.subtype)) := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  rw [Subgroup.card_map_of_injective H.subtype_injective]
  have h1 := Subgroup.relIndex_mul_relIndex ⊥ π.ker (W.comap π) bot_le (π.ker_le_comap W)
  have h2 : π.ker.relIndex (W.comap π) = Nat.card W := by
    rw [← MonoidHom.comap_bot, Subgroup.relIndex_comap,
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
      Subgroup.relIndex_bot_left]
  rw [h2, Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, QuotientGroup.ker_mk'] at h1
  rw [← h1]
  exact Nat.Coprime.mul_right (primeComplementCore_coprime p) hW

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneLieData.exists_sylowTwo_d1PlusCore (hd : D1OneLieData p P M H R Rbar K)
    {W : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hWC : W ≤ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)))
    (hW2 : IsPGroup 2 W)
    (hWidx : ¬ 2 ∣ (W.subgroupOf (Subgroup.centralizer
      (K : Set (H ⧸ primeComplementCore (G := H) p)))).index)
    (hRW : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤
      Subgroup.normalizer (W : Set (H ⧸ primeComplementCore (G := H) p))) :
    ∃ T : Subgroup G, T ≤ d1PlusCore p H K ∧ IsPGroup 2 T ∧
      ¬ 2 ∣ (T.subgroupOf (d1PlusCore p H K)).index ∧
      R ≤ Subgroup.normalizer (T : Set G) ∧ pCoreOf 2 H ≤ T := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p.Coprime 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hd.cfg.red.ne_two
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  set N := (W.comap π).map H.subtype
  have hNN : N ≤ d1PlusCore p H K := Subgroup.map_mono (Subgroup.comap_mono hWC)
  have hNcop : p.Coprime (Nat.card N) := by
    refine coprime_card_map_comap_mk H ?_
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hW2
    rw [hk]
    exact hp2.pow_right k
  have hRN : R ≤ Subgroup.normalizer (N : Set G) := by
    have hR' : R.subgroupOf H ≤ Subgroup.normalizer ((W.comap π : Subgroup H) : Set H) :=
      le_trans (fun r hr => hRW (hd.cfg.rbar ▸ Subgroup.mem_map_of_mem π hr))
        (Subgroup.le_normalizer_comap π)
    have hmap := Subgroup.map_mono (f := H.subtype) hR'
    rw [Subgroup.map_subgroupOf_eq_of_le hd.cfg.ext.le_H] at hmap
    exact hmap.trans (Subgroup.le_normalizer_map _)
  obtain ⟨T, hTN, hT2, hTidx, hRT⟩ :=
    exists_le_normalizer_of_coprime (q := 2) hd.cfg.ext.isPGroup hRN hNcop
  refine ⟨T, hTN.trans hNN, hT2, ?_, hRT, ?_⟩
  ·
    have hrel := Subgroup.relIndex_mul_relIndex T N (d1PlusCore p H K) hTN hNN
    have hNrel : N.relIndex (d1PlusCore p H K) = W.relIndex
        (Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))) := by
      rw [d1PlusCore, Subgroup.relIndex_map_map_of_injective _ _ H.subtype_injective,
        Subgroup.relIndex_comap,
        Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
    change ¬ 2 ∣ T.relIndex (d1PlusCore p H K)
    rw [← hrel, hNrel]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h' | h'
    · exact hTidx h'
    · exact hWidx h'
  ·
    have hSN : pCoreOf 2 H ≤ GLBPrimeCore p H := pCoreOf_le_glbPrimeCore Nat.prime_two hp2 H
    have hON : GLBPrimeCore p H ≤ N := by
      rw [← Subgroup.map_subgroupOf_eq_of_le (glbPrimeCore_le p H), glbPrimeCore_subgroupOf]
      refine Subgroup.map_mono fun x hx => ?_
      change π x ∈ W
      rw [show π x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
      exact W.one_mem
    have hTS : T ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
      (hTN.trans (Subgroup.map_subtype_le _)).trans
        (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H)
    have hST2 : IsPGroup 2 (pCoreOf 2 H ⊔ T : Subgroup G) := IsPGroup.to_sup_of_normal_left'
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H) hT2 hTS
    exact le_sup_left.trans
      (le_of_le_of_isPGroup_of_not_dvd_index le_sup_right (sup_le (hSN.trans hON) hTN) hST2 hTidx)

end PlusCore

end CFSG.AGLEmbedding
