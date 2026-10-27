module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineOne
import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGenRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

variable {G : Type} [Group G] [Finite G]

theorem QSet.mem_sigmaM_of_mem_sigmaA {M : Subgroup G} {p : ℕ} {Q : Subgroup G}
    (hQ : Q ∈ QSet M p) (hp : p ∈ rankThreeSigmaA G) : p ∈ sigmaM G M :=
  ⟨hp, (QSet.two_le_pRank_of_mem hQ).trans
    (pRank_mono p (QSet.prime_of_mem hQ).one_lt (QSet.le_of_mem hQ))⟩

theorem twoLocalPrimeRank_subgroup_le {p : ℕ} (hp : p.Prime) (H : Subgroup G) :
    twoLocalPrimeRank p H ≤ twoLocalPrimeRank p G := by
  refine csSup_le' ?_
  rintro _ ⟨L, ⟨P, hP1, hP2, rfl⟩, rfl⟩
  set L' : Subgroup G := normalizer ((P.map H.subtype : Subgroup G) : Set G) with hL'
  have hL'loc : IsTwoLocal L' := by
    refine ⟨P.map H.subtype, ?_,
      hP2.of_equiv (P.equivMapOfInjective H.subtype H.subtype_injective), rfl⟩
    intro h
    exact hP1 ((Subgroup.map_eq_bot_iff_of_injective P H.subtype_injective).mp h)
  have hle : (normalizer (P : Set H)).map H.subtype ≤ L' :=
    Subgroup.le_normalizer_map (H := P) H.subtype
  have h1 : CFSG.Open.pRank p (normalizer (P : Set H)) ≤ CFSG.Open.pRank p L' :=
    (CFSG.SectionRank.pRank_le_map hp.one_lt H.subtype H.subtype_injective _).trans
      (CFSG.SectionRank.pRank_mono hp.one_lt hle)
  refine h1.trans (le_csSup ⟨Nat.card G, ?_⟩ ⟨L', hL'loc, rfl⟩)
  rintro _ ⟨K, -, rfl⟩
  exact CFSG.SectionRank.pRank_le_card_of_one_lt hp.one_lt K

theorem mem_sigmaA_of_large (hrank : evenRank G = 3) {p : ℕ} (hp : p.Prime) (h5 : 5 < p)
    (hdvd : p ∣ Nat.card G) (h3 : rankThreeLocalRank p G = 3) : p ∈ rankThreeSigmaA G := by
  classical
  have hS1 : ¬ ({p | p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card G ∧ 3 < rankThreeLocalRank p G} :
      Set ℕ).Nonempty := by
    rintro ⟨q, hq, hq2, -, hlt⟩
    have := rankThreeLocalRank_le_evenRank (G := G) q hq hq2
    omega
  have hS2 : ({p | p.Prime ∧ 5 < p ∧ p ∣ Nat.card G ∧ rankThreeLocalRank p G = 3} :
      Set ℕ).Nonempty := ⟨p, hp, h5, hdvd, h3⟩
  dsimp only [rankThreeSigmaA]
  rw [if_neg hS1, if_pos hS2]
  exact ⟨hp, h5, hdvd, h3⟩

namespace NineSettingGen

variable {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}


theorem nineFiveGen (h : NineSettingGen G M p Q H E k) (hp : p ∉ sigmaM G M) :
    p ∉ rankThreeSigmaA G ∧
      (rankThreeLocalRank p H ≤ 3 ∧
        (rankThreeLocalRank p H = 3 → 4 ≤ evenRank G ∨ p ≤ 5)) ∧
      (pCoreOf 2 H ≠ ⊥ ∨ p = 3 →
        3 < rankThreeLocalRank 3 H → CFSG.Open.pRank 3 (H ⊓ M) < 2) := by
  have hA : p ∉ rankThreeSigmaA G := fun hσ => hp (QSet.mem_sigmaM_of_mem_sigmaA h.mem_Q hσ)
  have hoff := h.setting.cstar.off_sigma p h.prime h.ne_two hA
  have hle : rankThreeLocalRank p H ≤ rankThreeLocalRank p G := by
    unfold rankThreeLocalRank
    exact twoLocalPrimeRank_subgroup_le h.prime H
  refine ⟨hA, ⟨hle.trans hoff.1, fun h3 => hoff.2 (by omega)⟩, fun hO h3 => ?_⟩
  by_contra hnot
  push Not at hnot
  have h4 : 4 ≤ rankThreeLocalRank 3 G := by
    have h1 := twoLocalPrimeRank_subgroup_le Nat.prime_three H
    unfold rankThreeLocalRank at h1 h3 ⊢
    omega
  have h3A : 3 ∈ rankThreeSigmaA G :=
    CFSG.LocalAnalysis.AGL81TheoremCD.mem_sigmaA_of_four_le_localRank Nat.prime_three
      (by norm_num) h4
  have h3M : 3 ∈ sigmaM G M :=
    ⟨h3A, hnot.trans (pRank_mono 3 (by norm_num) inf_le_right)⟩
  rcases hO with hO | hp3
  · have hHN : H ≤ normalizer (pCoreOf 2 H : Set G) := localGroup_le_normalizer_pCoreOf 2 H
    have hloc : IsTwoLocal (normalizer (pCoreOf 2 H : Set G)) :=
      ⟨pCoreOf 2 H, hO, pCoreOf_isPGroup 2 H, rfl⟩
    have hmono : CFSG.Open.pRank 3 (H ⊓ M) ≤
        CFSG.Open.pRank 3 (normalizer (pCoreOf 2 H : Set G) ⊓ M) :=
      pRank_mono 3 (by norm_num) (le_inf (inf_le_left.trans hHN) inf_le_right)
    exact h.not_le (hHN.trans (h.setting.theoremE h3M hloc (by omega)))
  · exact hp (hp3 ▸ h3M)

end NineSettingGen

namespace NineSetting

variable {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}

theorem nineFive (h : NineSetting G M p Q H E k) (hp : p ∉ sigmaM G M) :
    p ∉ rankThreeSigmaA G ∧
      (rankThreeLocalRank p H ≤ 3 ∧ (rankThreeLocalRank p H = 3 → p ≤ 5)) ∧
      (3 < rankThreeLocalRank 3 H → CFSG.Open.pRank 3 (H ⊓ M) < 2) := by
  have hrank : evenRank G = 3 := h.setting.standing.rank
  have hA : p ∉ rankThreeSigmaA G := fun hσ => hp (QSet.mem_sigmaM_of_mem_sigmaA h.mem_Q hσ)
  have hbound : ∀ q : ℕ, q.Prime → q ≠ 2 → rankThreeLocalRank q H ≤ 3 := fun q hq hq2 => by
    have h1 := twoLocalPrimeRank_subgroup_le hq H
    have h2 := rankThreeLocalRank_le_evenRank (G := G) q hq hq2
    unfold rankThreeLocalRank at h2 ⊢
    omega
  refine ⟨hA, ⟨hbound p h.prime h.ne_two, fun h3 => ?_⟩, fun h3 => ?_⟩
  · by_contra h5
    have hG3 : rankThreeLocalRank p G = 3 := by
      have h1 := twoLocalPrimeRank_subgroup_le h.prime H
      have h2 := rankThreeLocalRank_le_evenRank (G := G) p h.prime h.ne_two
      unfold rankThreeLocalRank at h2 ⊢
      unfold rankThreeLocalRank at h3
      omega
    have hdvd : p ∣ Nat.card G := (mem_muSet h).2.2.1.trans (Subgroup.card_subgroup_dvd_card M)
    exact hA (mem_sigmaA_of_large hrank h.prime (by omega) hdvd hG3)
  · exact absurd h3 (by have := hbound 3 Nat.prime_three (by norm_num); omega)

end NineSetting


end CFSG.LocalAnalysis.RankThreeUC.AGL81C
