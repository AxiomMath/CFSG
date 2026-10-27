module

public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2FullCore
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2FullTransport
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Bar

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance

theorem input11_2Full_of_tables (T : Tables112) (TL : TableL2) (TT : Tables112Types) :
    Input11_2Full := by
  intro G _ _ m p hS X B L hB hBX hr hL hnL
  obtain ⟨hp, hp2, -, -⟩ := hS.beta
  have : Fact p.Prime := ⟨hp⟩
  have hXne : X ≠ ⊤ := by
    rintro rfl
    have : IsSimpleGroup G := hS.simple
    apply hnL
    rcases i112f_eq_bot_or_top_of_isSubnormal hL.2.1 with h | h
    · have hN : Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
        Subgroup.normalizer_eq_top_iff.2 inferInstance
      rw [h, hN]
      exact le_top
    · have hN : Subgroup.normalizer ((⊤ : Subgroup G) : Set G) = ⊤ :=
        Subgroup.normalizer_eq_top_iff.2 inferInstance
      rw [h, hN]
      exact le_top
  have hXK : CFSG.Open.IsKGroup ↥X := isKGroup_of_isKProper hS.kProper hXne
  set N : Subgroup ↥X := GLAPPrimeCore p ↥X with hNdef
  have hNc : ¬ p ∣ Nat.card N :=
    (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
  have hQK : CFSG.Open.IsKGroup (↥X ⧸ N) := isKGroup_quotient' hXK N
  have hQcore : GLAPPrimeCore p (↥X ⧸ N) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hBp : IsPGroup p B := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hB.2 g.1 g.2)⟩
  have hBel : IsElemAbelian p (barX p X B) := isElemAbelian_barX hB
  have hrankQ : GLATwoLocalRank p (↥X ⧸ N) ≤ CFSG.Open.pRank p (barX p X B) := by
    rw [rank_barX_of_isPGroup hp hBp hBX]
    exact (glaTwoLocalRank_quotient_le hp hp2 N hNc).trans hr
  have hLbar : GLAPComponent p ⊤ (barX p X L) :=
    i112b_glaPComponent_of_isComponentOf hQcore hL.2.2.1
  have hnLQ : ¬ barX p X B ≤ Subgroup.normalizer ((barX p X L : Subgroup (↥X ⧸ N)) :
      Set (↥X ⧸ N)) := by
    intro hle
    apply hnL
    intro b hb
    have h1 : QuotientGroup.mk' N ⟨b, hBX hb⟩ ∈
        Subgroup.normalizer ((barX p X L : Subgroup (↥X ⧸ N)) : Set (↥X ⧸ N)) :=
      hle ⟨⟨b, hBX hb⟩, (Subgroup.mem_subgroupOf).2 hb, rfl⟩
    have h2 : (⟨b, hBX hb⟩ : ↥X) ∈ (Subgroup.normalizer (L : Set G)).subgroupOf X := by
      rw [← i112f_comap_normalizer_barX hL]
      exact h1
    exact (Subgroup.mem_subgroupOf).1 h2
  obtain ⟨h3, hrel, haut, ⟨hZE, hZc⟩, htype⟩ :=
    i112f_core T TL TT hQK hp hp2 hQcore hBel hrankQ hLbar hnLQ
  subst h3
  have e : barOf 3 L ≃* ↥(barX 3 X L) := quotEquivBarX hp hL.1 hL.2.1
  refine ⟨rfl, (i112f_relIndex_barX hL hBX).symm.trans hrel, ?_, ?_, ?_⟩
  · rw [i112f_pRank_mulAut_of_mulEquiv e]
    exact haut
  · rw [i112f_barX_bClosure hBX hL.1]
    exact ⟨i112f_isElemAbelian_center hZE, (i112f_card_center _).trans_le hZc⟩
  · rcases htype with h | h | h | h | h | h
    · exact Or.inl (i112f_isLTwoOddPow_of_mulEquiv e.symm h)
    · exact Or.inr (Or.inl (i112f_isHatSix_of_mulEquiv e.symm h))
    · exact Or.inr (Or.inr (Or.inl (i112f_isHatSeven_of_mulEquiv e.symm h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (i112f_isHatMTwentyTwo_of_mulEquiv e.symm h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (i112f_isSLThreeExc_of_mulEquiv e.symm h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (i112f_isSUThreeExc_of_mulEquiv e.symm h))))))

end CFSG.HardMathSupport.Solomon.Coordinator
