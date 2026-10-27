module

public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2FullCore
import CFSG.HardMathSupport.Solomon.Coordinator.I11_2FullTransport
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Bar

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance

theorem i112_types_of_isKGroup (T : Tables112) (TL : TableL2) (TT : Tables112Types)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type} [Group Ω] [Finite Ω]
    (hΩ : CFSG.Open.IsKGroup Ω) {B L : Subgroup Ω} (hB : IsElemAbelian p B)
    (hr : GLATwoLocalRank p Ω ≤ CFSG.Open.pRank p B) (hL : GLAPComponent p ⊤ L)
    (hnL : ¬ B ≤ Subgroup.normalizer (L : Set Ω)) :
    p = 3 ∧ (Subgroup.normalizer (L : Set Ω)).relIndex B = 3 ∧
      (IsLTwoOddPow (barOf 3 L) ∨
        CFSG.HardMathSupport.Solomon.LocalBalance.IsHatSix (barOf 3 L) ∨
        IsHatSeven (barOf 3 L) ∨ IsHatMTwentyTwo (barOf 3 L) ∨
        IsSLThreeExc (barOf 3 L) ∨ IsSUThreeExc (barOf 3 L)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hXK : CFSG.Open.IsKGroup ↥(⊤ : Subgroup Ω) := hΩ.subgroup ⊤
  set N : Subgroup ↥(⊤ : Subgroup Ω) := GLAPPrimeCore p ↥(⊤ : Subgroup Ω) with hNdef
  have hNc : ¬ p ∣ Nat.card N :=
    (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
  have hBp : IsPGroup p B := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hB.2 g.1 g.2)⟩
  have hQK : CFSG.Open.IsKGroup (↥(⊤ : Subgroup Ω) ⧸ N) :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_quotient' hXK N
  have hQcore : GLAPPrimeCore p (↥(⊤ : Subgroup Ω) ⧸ N) = ⊥ :=
    CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCore_quotient_eq_bot hp
  have hBel : IsElemAbelian p (barX p ⊤ B) :=
    CFSG.LocalAnalysis.GLTheoremB.isElemAbelian_barX hB
  have hrankQ : GLATwoLocalRank p (↥(⊤ : Subgroup Ω) ⧸ N) ≤
      CFSG.Open.pRank p (barX p ⊤ B) := by
    rw [CFSG.LocalAnalysis.GLTheoremB.rank_barX_of_isPGroup hp hBp le_top]
    exact (CFSG.LocalAnalysis.GLTheoremB.glaTwoLocalRank_quotient_le hp hp2 N hNc).trans
      ((CFSG.HardMathSupport.Solomon.LocalBalance.glaTwoLocalRank_subgroup_le hp ⊤).trans hr)
  have hLbar : GLAPComponent p ⊤ (barX p ⊤ L : Subgroup (↥(⊤ : Subgroup Ω) ⧸ N)) :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.i112b_glaPComponent_of_isComponentOf
      hQcore hL.2.2.1
  have hnLQ : ¬ (barX p ⊤ B : Subgroup (↥(⊤ : Subgroup Ω) ⧸ N)) ≤
      Subgroup.normalizer ((barX p ⊤ L : Subgroup (↥(⊤ : Subgroup Ω) ⧸ N)) :
        Set (↥(⊤ : Subgroup Ω) ⧸ N)) := by
    intro hle
    apply hnL
    intro b hb
    have h1 : QuotientGroup.mk' N ⟨b, Subgroup.mem_top b⟩ ∈
        Subgroup.normalizer ((barX p ⊤ L : Subgroup (↥(⊤ : Subgroup Ω) ⧸ N)) :
          Set (↥(⊤ : Subgroup Ω) ⧸ N)) :=
      hle ⟨⟨b, Subgroup.mem_top b⟩, (Subgroup.mem_subgroupOf).2 hb, rfl⟩
    have h2 : (⟨b, Subgroup.mem_top b⟩ : ↥(⊤ : Subgroup Ω)) ∈
        (Subgroup.normalizer (L : Set Ω)).subgroupOf ⊤ := by
      rw [← CFSG.HardMathSupport.Solomon.Coordinator.i112f_comap_normalizer_barX hL]
      exact h1
    exact (Subgroup.mem_subgroupOf).1 h2
  obtain ⟨h3, hrel, -, -, htype⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.i112f_core T TL TT hQK hp hp2 hQcore hBel
      hrankQ hLbar hnLQ
  subst h3
  have e : barOf 3 L ≃* ↥(barX 3 ⊤ L) :=
    CFSG.LocalAnalysis.GLTheoremB.quotEquivBarX Nat.prime_three (le_top : L ≤ ⊤) hL.2.1
  refine ⟨rfl, (CFSG.HardMathSupport.Solomon.Coordinator.i112f_relIndex_barX hL
    (le_top : B ≤ ⊤)).symm.trans hrel, ?_⟩
  rcases htype with h | h | h | h | h | h
  · exact Or.inl
      (CFSG.HardMathSupport.Solomon.Coordinator.i112f_isLTwoOddPow_of_mulEquiv e.symm h)
  · exact Or.inr (Or.inl
      (CFSG.HardMathSupport.Solomon.Coordinator.i112f_isHatSix_of_mulEquiv e.symm h))
  · exact Or.inr (Or.inr (Or.inl
      (CFSG.HardMathSupport.Solomon.Coordinator.i112f_isHatSeven_of_mulEquiv e.symm h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (CFSG.HardMathSupport.Solomon.Coordinator.i112f_isHatMTwentyTwo_of_mulEquiv e.symm h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (CFSG.HardMathSupport.Solomon.Coordinator.i112f_isSLThreeExc_of_mulEquiv e.symm h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (CFSG.HardMathSupport.Solomon.Coordinator.i112f_isSUThreeExc_of_mulEquiv e.symm h)))))

theorem catalogIs_weakExcIndex_of_isL2TwoPowOdd {X : Type} [Group X] (h : IsL2TwoPowOdd X) :
    catalogIs X weakExcIndex := by
  obtain ⟨n, hn, hn1, ⟨e⟩⟩ := h
  have hpos : 0 < n := by omega
  have hv : (TauCeti.LieTypeIndex.A 1 ⟨2, n, Nat.prime_two, hpos⟩).Valid := by
    obtain ⟨k, hk⟩ := hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    simp only [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff, TauCeti.PrimePower.card_def]
    have h8 : 2 ^ (m + 3) = 8 * 2 ^ m := by ring
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    omega
  refine ⟨TauCeti.CFSGIndex.lie ⟨.A 1 ⟨2, n, Nat.prime_two, hpos⟩, hv⟩,
    Or.inr ⟨rfl, hn, hn1⟩, ⟨?_⟩⟩
  exact e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1
    ⟨2, n, Nat.prime_two, hpos⟩ hv).symm

end CFSG.LocalAnalysis.GLTheoremA

end
