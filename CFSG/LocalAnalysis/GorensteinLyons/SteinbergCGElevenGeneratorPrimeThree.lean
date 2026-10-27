module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXLargeLocalRankCore

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.Open
open CFSG.LargeEvenClassification.Helpers (pGeneratorRank pGeneratorRank_le_generators)

namespace SteinbergCG

theorem pGeneratorRank_le_card_of_closure_eq {G : Type*} [Group G] [Finite G] {Q : Subgroup G}
    (hQ : IsPGroup 2 Q) {S : Finset G} (hS : closure (S : Set G) = Q) :
    pGeneratorRank 2 Q ≤ S.card := by
  classical
  subst hS
  have h := pGeneratorRank_le_generators Nat.prime_two hQ
    (S.preimage ((↑) : closure (S : Set G) → G) Subtype.val_injective.injOn) (by
      rw [Finset.coe_preimage]
      exact closure_closure_coe_preimage)
  refine h.trans (Finset.card_le_card_of_injOn Subtype.val (fun a ha => ?_)
    Subtype.val_injective.injOn)
  exact Finset.mem_preimage.mp ha

theorem eq_three_of_orderOf_two_eq_two {p : ℕ} (hp : p.Prime) (h : orderOf (2 : ZMod p) = 2) :
    p = 3 := by
  have := Fact.mk hp
  have h1 : ((3 : ℕ) : ZMod p) = 0 := by
    have h2 := pow_orderOf_eq_one (2 : ZMod p)
    rw [h] at h2
    have e : ((3 : ℕ) : ZMod p) = (2 : ZMod p) ^ 2 - 1 := by
      push_cast
      ring
    rw [e, h2, sub_self]
  rw [ZMod.natCast_eq_zero_iff] at h1
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h1

end SteinbergCG

open SteinbergCG in
theorem eleven_generator_two_subgroups_force_large_odd_local_prime_three
    {G : Type*} [Group G]
    [Finite G] (hchar : CFSG.IsCharacteristicPType G 2) (he : 4 ≤ CFSG.twoLocalOddRank G)
    (hgen : ∀ P : Subgroup G, IsPGroup 2 P →
      ∃ S : Finset G, S.card ≤ 11 ∧ closure (S : Set G) = P) :
    (∀ p : ℕ, p.Prime → p ≠ 2 → 4 ≤ GLATwoLocalRank p G → p = 3) ∧
      CFSG.twoLocalOddRank G = GLATwoLocalRank 3 G ∧ 4 ≤ GLATwoLocalRank 3 G := by
  have := Fact.mk Nat.prime_two
  obtain ⟨-, -, hlocal, -⟩ := large_local_rank_core_and_component_reduction hchar (by omega)
  have hbridge : ∀ (q : ℕ) (K : Subgroup G), CFSG.pRank q K = CFSG.Open.pRank q K :=
    fun q K => (CFSG.SectionRank.pRank_eq_open_pRank_top q K).trans
      (CFSG.SectionRank.pRank_eq_pRank_top_subgroup K).symm
  have hbddL : ∀ p : ℕ, 1 < p →
      BddAbove {k | ∃ H : Subgroup G, IsTwoLocal H ∧ CFSG.Open.pRank p H = k} := by
    intro p hp
    refine ⟨Nat.card G, ?_⟩
    rintro _ ⟨K, -, rfl⟩
    obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank hp K
    have h1 : CFSG.Open.pRank p K < p ^ CFSG.Open.pRank p K := Nat.lt_pow_self hp
    have h2 : Nat.card E ≤ Nat.card G := card_le_card_group E
    omega
  have hlarge : ∀ p : ℕ, p.Prime → p ≠ 2 → 4 ≤ GLATwoLocalRank p G → p = 3 := by
    intro p hp hp2 h4
    have := Fact.mk hp
    have hne : {k | ∃ H : Subgroup G, IsTwoLocal H ∧ CFSG.Open.pRank p H = k}.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      have h0 : GLATwoLocalRank p G = 0 := by
        rw [GLATwoLocalRank, CFSG.Open.twoLocalPrimeRank, h]
        exact csSup_empty
      omega
    obtain ⟨K, ⟨T, hT1, hT2, rfl⟩, hrank⟩ := Nat.sSup_mem hne (hbddL p hp.one_lt)
    obtain ⟨A, hAK, hA, hAcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (normalizer (T : Set G))
    have hs : 4 ≤ CFSG.Open.pRank p (normalizer (T : Set G)) := by
      rw [hrank]
      exact h4
    obtain ⟨⟨d, hd, hfd⟩, -, -⟩ :=
      hlocal p hp hp2 A _ hA hAcard (by omega) T hT1 hT2 hAK
    have hQ2 : IsPGroup 2 (CFSG.inSubgroup (CFSG.pCore 2) (normalizer (T : Set G))) :=
      CFSG.pCore_isPGroup.map _
    obtain ⟨S, hS11, hS⟩ := hgen _ hQ2
    have hdQ := pGeneratorRank_le_card_of_closure_eq hQ2 hS
    rw [pGeneratorRank, hd, Nat.log_pow (by norm_num)] at hdQ
    have hf2 := CFSG.PreuniquenessRankFour.Helpers.binary_prime_order_at_least_two p hp2
    have hf : orderOf (2 : ZMod p) = 2 := by
      by_contra hne2
      have h3 : 3 ≤ orderOf (2 : ZMod p) := by omega
      have := Nat.mul_le_mul h3 hs
      omega
    exact eq_three_of_orderOf_two_eq_two hp hf
  have hbddE : BddAbove {r : ℕ | ∃ K : Subgroup G, CFSG.IsPLocal 2 K ∧
      ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ Nat.card G ∧ r = CFSG.pRank q K} := by
    refine ⟨Nat.card G, ?_⟩
    rintro _ ⟨K, -, q, hq, -, -, rfl⟩
    rw [hbridge]
    obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank hq.one_lt K
    have h1 : CFSG.Open.pRank q K < q ^ CFSG.Open.pRank q K := Nat.lt_pow_self hq.one_lt
    have h2 : Nat.card E ≤ Nat.card G := card_le_card_group E
    omega
  have hneE : {r : ℕ | ∃ K : Subgroup G, CFSG.IsPLocal 2 K ∧
      ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ Nat.card G ∧ r = CFSG.pRank q K}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have h0 : CFSG.twoLocalOddRank G = 0 := by
      rw [CFSG.twoLocalOddRank, h]
      exact csSup_empty
    omega
  obtain ⟨K, ⟨T, hT1, hT2, rfl⟩, p, hp, hp2, -, hrank⟩ := Nat.sSup_mem hneE hbddE
  have he' : CFSG.twoLocalOddRank G = CFSG.Open.pRank p (normalizer (T : Set G)) := by
    rw [← hbridge]
    exact hrank
  have hge : CFSG.twoLocalOddRank G ≤ GLATwoLocalRank p G := by
    rw [he']
    exact le_csSup (hbddL p hp.one_lt) ⟨_, ⟨T, hT1, hT2, rfl⟩, rfl⟩
  have hp3 : p = 3 := hlarge p hp hp2 (he.trans hge)
  subst hp3
  have hle : GLATwoLocalRank 3 G ≤ CFSG.twoLocalOddRank G := by
    have hne3 : {k | ∃ H : Subgroup G, IsTwoLocal H ∧ CFSG.Open.pRank 3 H = k}.Nonempty :=
      ⟨_, ⟨_, ⟨T, hT1, hT2, rfl⟩, rfl⟩⟩
    obtain ⟨K', ⟨T', hT'1, hT'2, rfl⟩, hrank'⟩ := Nat.sSup_mem hne3 (hbddL 3 (by norm_num))
    have hpos : 1 ≤ CFSG.Open.pRank 3 (normalizer (T' : Set G)) := by
      rw [hrank']
      exact le_trans (by norm_num) (he.trans hge)
    obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3)
      (normalizer (T' : Set G))
    have h3G : 3 ∣ Nat.card G := by
      have h1 : 3 ∣ Nat.card E := by
        rw [hE]
        exact dvd_pow_self 3 (by omega)
      exact h1.trans (card_subgroup_dvd_card E)
    rw [GLATwoLocalRank, CFSG.Open.twoLocalPrimeRank, ← hrank']
    refine le_csSup hbddE ⟨_, ⟨T', hT'1, hT'2, rfl⟩, 3, Nat.prime_three, by norm_num, h3G, ?_⟩
    exact (hbridge 3 _).symm
  exact ⟨hlarge, le_antisymm hge hle, he.trans hge⟩

end CFSG.LocalAnalysis.GorensteinLyons
