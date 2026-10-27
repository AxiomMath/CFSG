module

public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockStructure

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Package

variable {G : Type} [Group G] [Finite G]

theorem D1L2Data.isElemAbelian {p n : ℕ} [Fact p.Prime] {P : Sylow p G} {M H R X : Subgroup G}
    (h : D1L2Data p n P M H R X) : IsElemAbelian p X := by
  obtain ⟨φ, -⟩ := h.torus
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a', rfl⟩ := φ.surjective a
    obtain ⟨b', rfl⟩ := φ.surjective b
    rw [← map_mul, ← map_mul, mul_comm]
  · obtain ⟨a, ha⟩ := φ.surjective ⟨x, hx⟩
    have hap : a ^ p = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
    have : (⟨x, hx⟩ : X) ^ p = 1 := by rw [← ha, ← map_pow, hap, map_one]
    simpa using congrArg Subtype.val this

theorem D1L2Data.card_eq {p n : ℕ} [Fact p.Prime] {P : Sylow p G} {M H R X : Subgroup G}
    (h : D1L2Data p n P M H R X) : Nat.card X = p ^ n := by
  obtain ⟨φ, -⟩ := h.torus
  rw [← Nat.card_congr φ.toEquiv, Nat.card_congr Multiplicative.toAdd,
    GaloisField.card p n (by have := h.three_le; omega)]

theorem D1L2Data.le_inf_normalizer {p n : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R X : Subgroup G} (h : D1L2Data p n P M H R X) :
    X ≤ M ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
  h.ph3.inf_eq_inf_normalizer_twoCore ▸ h.le_R.trans h.ph3.le_inf

theorem D1L2Data.coprime_of_perfect {p n : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R X : Subgroup G} (h : D1L2Data p n P M H R X) :
    ∀ Y : Subgroup G, Y ≤ M ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G) → ⁅Y, Y⁆ = Y →
      p.Coprime (Nat.card Y) := by
  intro Y hY hperf
  have hYN := h.perfect_le Y (h.ph3.inf_eq_inf_normalizer_twoCore ▸ hY) hperf
  exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hYN)
    (glbPrimeCore_coprime p H)

end Package

theorem stmtNormalizeBlocks_of (hX3 : StmtXNormalizesBlockThree) (hRank : StmtComponentRank)
    (hLift : StmtBarPRankLift) : StmtNormalizeBlocks := by
  intro G _ _ p n _ P M H R X h hp hB3 r t hr hnr h5r htK htr L hL
  have : Fact r.Prime := ⟨hr⟩
  have hGP : 5 ≤ p → 4 ≤ Open.pRank 3 (H ⊓ M) → False := fun hp5 h4 =>
    h.false_of_four_le_pRank Nat.prime_three (by decide) (by omega) h4
  refine ⟨?_, ?_⟩
  · rcases hp with hp3 | hp5
    · exact hX3 h hp3 L hL (hB3 L hL)
    · intro x hxX
      by_contra hxL
      have hxp : IsPGroup p (Subgroup.zpowers x) :=
        isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using h.isElemAbelian.2 x hxX)
      have hle := h.le_pRank_three_of_not_mem_normalizer hRank hLift hB3
        (h.le_R.trans h.ph3.le_inf hxX) hxp hL hxL
      exact hGP hp5 (by omega)
  · by_contra htL
    have hle := h.le_pRank_three_of_not_mem_normalizer hRank hLift hB3 htK htr hL htL
    rcases hp with hp3 | hp5
    · have := h.pRank_le
      subst hp3
      omega
    · exact hGP hp5 (by omega)

theorem stmtROne_of (hB3 : StmtBlockThree)
    (hLB : StmtLemmaB) (hT1 : StmtPPDElement) (hNB : StmtNormalizeBlocks)
    (h85' : Asc81bEightFive) (hD2 : D1NoXBlock) : StmtROne := by
  intro G _ _ p n _ P M H R X h hp L hL
  obtain ⟨r, t, hr, hnr, hr2, hr3, hrp, hrp1, htK, htX, htr, htr1, htnt, hirr⟩ := hT1 h
  have h5r : 5 ≤ r := hr.five_le_of_ne_two_of_ne_three hr2 hr3
  obtain ⟨hXL, htL⟩ := hNB h hp (fun L' hL' => hB3 h.ph3 hL') r t hr hnr h5r htK htr L hL
  have hpp : p.Prime := Fact.out
  obtain ⟨hnot1, -⟩ := h.ph3.nineThree_not_one h85' hD2 hL
  exact hLB G M (pCoreOf 2 H) L X p r t h.ph3.isKGroup.1 h.ph3.asc81bHyp hL hnot1
    (h.ph3.not_isSylowTwoOf_inf h85' hD2 hL) hpp h.ph3.ne_two h.coprime_of_perfect
    h.le_inf_normalizer hXL h.isElemAbelian
    (by rw [h.card_eq]; exact Nat.pow_le_pow_right hpp.pos h.three_le)
    (h.ph3.inf_eq_inf_normalizer_twoCore ▸ htK) htL htX hr hr2 hr3 hrp hrp1 htr1 htnt
    (fun Y hYX hYt => hirr 1 (by simpa using hr.one_lt.ne') Y hYX (by simpa using hYt))

end CFSG.AGLEmbedding
