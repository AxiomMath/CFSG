module

public import CFSG.GH74.GLS.Stage4.RestZFH1
public import CFSG.GH74.GLS.Stage4.RestZFH2

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4
  CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage4.Rest.L92

theorem Ch6Pre.outPlus6 {G : Type} [Group G] [Finite G] {D : Ch6Notation G} (hnot : ¬ D.AllX2)
    (hH : D.HIdx) (hZ : Ch6ZFusionAll) (hD : Ch6Pre D) : Ch6OutPlus G := by
  rcases hD.core_or_allX2' with ⟨hc, hs⟩ | ⟨hc, hs⟩ | h
  · exact (Ch6Post.mk hc (hc.l92_of_shapeStd hs)
      (hc.zclass_of_zfusion (hZ G D hc hs hH))).outPlus
  · exact (Ch6Post.mk hc (hc.l92_of_shapeStd hs)
      (hc.zclass_of_zfusion (hZ G D.mirror hc hs hH.mirror))).outPlus
  · exact (hnot h).elim

theorem ch6Case9Plus_of_H (hGood : Ch6T2Good9XH) (hBad : Ch6T2Bad9) (hZ : Ch6ZFusionAll) :
    Ch6Case9Plus := by
  intro G _ _ hStd hr Gs _ hAt
  by_cases hb : Ch6Bad3 G
  · exact (hBad G hStd hr Gs hAt hb).elim
  · obtain ⟨D, hD, hnot, hH⟩ := hGood G hStd hr Gs hAt hb
    exact hD.outPlus6 hnot hH hZ

theorem ch6CaseGt9Plus_of_H (hGood : Ch6T2GoodGt9XH) (hBad : Ch6T2BadGt9) (hZ : Ch6ZFusionAll) :
    Ch6CaseGt9Plus := by
  intro G _ _ hStd hr Gs _ n hn hAt
  by_cases hb : Ch6Bad3 G
  · exact (hBad G hStd hr Gs n hn hAt hb).elim
  · obtain ⟨D, hD, hnot, hH⟩ := hGood G hStd hr Gs n hn hAt hb
    exact hD.outPlus6 hnot hH hZ

theorem ch6CaseRestPlus_of_H (hT2 : Ch6RestT2SH) (hZ : Ch6ZFusionAll) : Ch6CaseRestPlus := by
  intro G _ _ hStd hr Gs _ q₁ q₂ hAt h99 hn
  obtain ⟨D, hD, hS, hH⟩ := hT2 G hStd hr Gs q₁ q₂ hAt h99 hn
  exact hD.outPlus6 (fun hA => hD.noAllX2 hS hA) hH hZ

theorem ch6OutPlus_of_H (hT2 : Ch6RestT2SH) (hG9 : Ch6T2Good9XH) (hB9 : Ch6T2Bad9)
    (hGGt9 : Ch6T2GoodGt9XH) (hBGt9 : Ch6T2BadGt9) (hZ : Ch6ZFusionAll) {G : Type} [Group G]
    [Finite G] (hStd : Std G) (hr : pRank 2 G = 3) {Gs : Type} [Group Gs]
    (hG2 : IsTwoCentralG2TypeG2 G Gs) : Ch6OutPlus G :=
  ch6OutPlus_of_cases (ch6Case9Plus_of_H hG9 hB9 hZ) (ch6CaseGt9Plus_of_H hGGt9 hBGt9 hZ)
    (ch6CaseRestPlus_of_H hT2 hZ) hStd hr hG2

end CFSG.GH74.GLS.Stage4.Rest
