module

public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2VCore
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2FullTransport
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Bar
public import CFSG.LocalAnalysis.GLTheoremA.PartI.ExcBridge
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4XN

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.ComponentBalance
  CFSG.HardMathSupport.Solomon.Coordinator

variable {G : Type} [Group G] [Finite G]

private theorem bar_red {X B L : Subgroup G} (hX : CFSG.Open.IsKGroup ↥X) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hB : IsElemAbelian p B) (hBX : B ≤ X)
    (hr : GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B) (hL : GLAPComponent p X L)
    (hnL : ¬ B ≤ Subgroup.normalizer (L : Set G)) :
    CFSG.Open.IsKGroup (↥X ⧸ GLAPPrimeCore p ↥X) ∧
      GLAPPrimeCore p (↥X ⧸ GLAPPrimeCore p ↥X) = ⊥ ∧ IsElemAbelian p (barX p X B) ∧
      GLATwoLocalRank p (↥X ⧸ GLAPPrimeCore p ↥X) ≤ CFSG.Open.pRank p (barX p X B) ∧
      GLAPComponent p ⊤ (barX p X L) ∧
      ¬ barX p X B ≤ Subgroup.normalizer ((barX p X L : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) :
        Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
  have : Fact p.Prime := ⟨hp⟩
  set N : Subgroup ↥X := GLAPPrimeCore p ↥X with hNdef
  have hNc : ¬ p ∣ Nat.card N :=
    (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
  have hBp : IsPGroup p B := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hB.2 g.1 g.2)⟩
  refine ⟨isKGroup_quotient' hX N, glaPPrimeCore_quotient_eq_bot hp,
    isElemAbelian_barX hB, ?_, i112b_glaPComponent_of_isComponentOf
      (glaPPrimeCore_quotient_eq_bot hp) hL.2.2.1, ?_⟩
  · rw [rank_barX_of_isPGroup hp hBp hBX]
    exact (glaTwoLocalRank_quotient_le hp hp2 N hNc).trans hr
  · intro hle
    apply hnL
    intro b hb
    have h1 : QuotientGroup.mk' N ⟨b, hBX hb⟩ ∈
        Subgroup.normalizer ((barX p X L : Subgroup (↥X ⧸ N)) : Set (↥X ⧸ N)) :=
      hle ⟨⟨b, hBX hb⟩, (Subgroup.mem_subgroupOf).2 hb, rfl⟩
    have h2 : (⟨b, hBX hb⟩ : ↥X) ∈ (Subgroup.normalizer (L : Set G)).subgroupOf X := by
      rw [← i112f_comap_normalizer_barX hL]
      exact h1
    exact (Subgroup.mem_subgroupOf).1 h2

private theorem valid_A_one_two_pow (n : ℕ) (hn : Odd n) (hn1 : 1 < n) (hpos : 0 < n) :
    (TauCeti.LieTypeIndex.A 1 ⟨2, n, Nat.prime_two, hpos⟩).Valid := by
  obtain ⟨k, hk⟩ := hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simp only [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff, TauCeti.PrimePower.card_def]
  have h8 : 2 ^ (m + 3) = 8 * 2 ^ m := by ring
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  omega

private theorem weakExc_of_isL2TwoPowOdd {Y : Type} [Group Y] (h : IsL2TwoPowOdd Y) :
    catalogIs Y weakExcIndex := by
  obtain ⟨n, hn, hn1, ⟨e⟩⟩ := h
  have hpos : 0 < n := by omega
  have hv := valid_A_one_two_pow n hn hn1 hpos
  refine ⟨TauCeti.CFSGIndex.lie ⟨.A 1 ⟨2, n, Nat.prime_two, hpos⟩, hv⟩, ?_,
    ⟨e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 ⟨2, n, Nat.prime_two, hpos⟩
      hv).symm⟩⟩
  exact Or.inr ⟨rfl, hn, hn1⟩

private theorem exc_shape_of_five {Y : Type} [Group Y] (hY : CFSG.Open.IsQuasisimple Y)
    (h : IsHatSix Y ∨ IsHatSeven Y ∨ IsHatMTwentyTwo Y ∨ IsSLThreeExc Y ∨ IsSUThreeExc Y) :
    IsExcShape Y := by
  refine isExcShape_of_types hY ?_
  rcases h with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem weakExc_of_not_normalizes (T : Tables112) (TL : TableL2) (TT : Tables112Types)
    (TM : Tables112More) {X B L : Subgroup G} (hX : CFSG.Open.IsKGroup ↥X)
    (hB : IsElemAbelian 3 B) (hBX : B ≤ X) (hr : GLATwoLocalRank 3 ↥X ≤ CFSG.Open.pRank 3 B)
    (hL : GLAPComponent 3 X L) (hnL : ¬ B ≤ Subgroup.normalizer (L : Set G)) :
    catalogIs (PSimple 3 L) weakExcIndex := by
  obtain ⟨hQK, hQcore, hBel, hrankQ, hLbar, hnLQ⟩ :=
    bar_red hX Nat.prime_three (by norm_num) hB hBX hr hL hnL
  obtain ⟨-, -, -, -, -, hcase⟩ :=
    i112v_core T TL TT TM hQK Nat.prime_three (by norm_num) hQcore hBel hrankQ hLbar hnLQ
  have e : PQuot 3 L ≃* ↥(barX 3 X L) := quotEquivBarX Nat.prime_three hL.1 hL.2.1
  have eS : PSimple 3 L ≃* (↥(barX 3 X L) ⧸ Subgroup.center ↥(barX 3 X L)) :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  rcases hcase with ⟨hc1, -, -, hiso⟩ | ⟨hc3, htypes, -⟩
  ·
    have hcen : Subgroup.center ↥(barX 3 X L) = ⊥ := Subgroup.eq_bot_of_card_eq _ hc1
    have eZ : ↥(barX 3 X L) ⧸ Subgroup.center ↥(barX 3 X L) ≃* ↥(barX 3 X L) :=
      (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
    exact (catalogIs_congr (eS.trans eZ)).2
      (weakExc_of_isL2TwoPowOdd (isL2TwoPowOdd_of_isLTwoOddPow hiso))
  ·
    have hQL := i116e_isQuasisimple hQcore hLbar
    have hexc : IsExcShape ↥(barX 3 X L) := exc_shape_of_five hQL htypes
    obtain ⟨i, hi, f⟩ := hexc.2
    exact (catalogIs_congr eS).2 ⟨i, Or.inl hi, f⟩

end CFSG.LocalAnalysis.GLTheoremA.D4XN
