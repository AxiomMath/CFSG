module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.I112Ctx
public import CFSG.LocalAnalysis.GLTheoremA.PartI.BmaxCent
public import CFSG.LocalAnalysis.GLTheoremA.PartI.ExcBridge
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Red
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_CaseJK
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_CaseJgt
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_MinT
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_NR
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_Red
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_TablesB

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance

variable {G : Type} [Group G] [Finite G]

theorem kernel11_3a_of_tables (T : Tables112) (TL : TableL2) : Kernel11_3a :=
  kernel11_3a_of_core (i112_of_red (i112Red_of_tables T TL)) (noL2RankBound_of_tables tables113)
    (noL2Reduced_of_cases tables113 minT113_proved (caseJK113_of_tables tables113)
      (caseJgt113_of_tables tables113))

theorem i1131At_of_tables (T : Tables112) (TL : TableL2) (TT : Tables112Types)
    (hsimple : IsSimpleGroup G) (hKP : CFSG.Open.IsKProper G) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : I1131At G p := by
  intro B y K hB hy hK hnK
  set X : Subgroup G := Subgroup.centralizer ({y} : Set G)
  have hBX : B ≤ X := le_centralizer_of_mem hB.1 hy.1
  obtain ⟨-, hBmax⟩ := glaIsBmax_subgroupOf_centralizer hp hB hy
  have hr : GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B :=
    glaTwoLocalRank_le_pRank_of_isBmax hp hB X
  obtain ⟨hXne, h3, hrel, htype⟩ := i112c_types T TL TT hsimple hKP hp hp2 hB.1 hBX hr hK hnK
  subst h3
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 K) := isQuasisimple_pQuot_of_glaPComponent hp hK
  have hKX : K ≤ X := hK.1
  have hnL2 : ¬ IsLTwoOddPow (barOf 3 K) := fun hL2 =>
    kernel11_3a_of_tables T TL ↥X (isKGroup_of_isKProper hKP hXne) (B.subgroupOf X) hBmax
      (K.subgroupOf X) (glaPComponent_top_subgroupOf hp hK)
      (fun h => hnK ((le_normalizer_subgroupOf_iff hKX hBX).1 h))
      ((relIndex_normalizer_subgroupOf hKX hBX).trans hrel)
      (isL2TwoPowOdd_of_mulEquiv (pQuotSubgroupOfEquiv 3 hKX).symm
        (isL2TwoPowOdd_of_isLTwoOddPow hL2))
  rcases htype with h | h | h | h | h | h | h
  · exact absurd h hnL2
  · exact ⟨rfl, isExcShape_of_types hq (Or.inl h)⟩
  · exact ⟨rfl, isExcShape_of_types hq (Or.inr (Or.inl h))⟩
  · exact ⟨rfl, isExcShape_of_types hq (Or.inr (Or.inr (Or.inl h)))⟩
  · exact ⟨rfl, isExcShape_of_types hq (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩
  · exact ⟨rfl, isExcShape_of_types hq (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))⟩
  · exact ⟨rfl, isExcShape_of_types hq (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))⟩

end CFSG.LocalAnalysis.GLTheoremA
