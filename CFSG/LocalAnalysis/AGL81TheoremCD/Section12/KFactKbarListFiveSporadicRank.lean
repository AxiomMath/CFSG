module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactKbarListFiveTransport
import CFSG.Sporadic.McL.Simple
import CFSG.Sporadic.Fi22.Simple
import CFSG.Sporadic.Co1
import CFSG.Sporadic.Co2
import CFSG.Sporadic.Co3
import CFSG.Sporadic.B
import CFSG.Sporadic.HN
import CFSG.Sporadic.Fi24.Simple

public import CFSG.LocalAnalysis.SectionRank.Sporadic.B
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Co1
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Co2
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Co3
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Fi22
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Fi24prime
public import CFSG.LocalAnalysis.SectionRank.Sporadic.HN
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Ly
public import CFSG.LocalAnalysis.SectionRank.Sporadic.McL
public import CFSG.LocalAnalysis.SectionRank.Sporadic.ON
import CFSG.Sporadic.Ly.Primitive
import CFSG.Sporadic.ON.Simple

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KbarListFive

open CFSG.Open CFSG.Blueprint.NativeSporadic Subgroup

theorem false_of_rank_four_model {K S T : Type} [Group K] [Finite K] [Group S] [Finite S]
    [Group T] [Finite T] [IsSimpleGroup T] (hq : CFSG.IsQuasisimple K)
    (e : K ⧸ center K ≃* S) (a : K ≃* T)
    (hT : ∃ E : Subgroup T, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4)
    {Y : Subgroup (MulAut S)} (hY : (MulAut.conj : S →* MulAut S).range ≤ Y)
    (hr : CFSG.Open.pRank 3 Y ≤ 3) : False := by
  have : IsSimpleGroup K := a.isSimpleGroup
  have hK := (pRank_top_le_of_centerQuotient hq e (by norm_num) hY).trans hr
  obtain ⟨E, hE, hc⟩ := hT
  have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup T) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_top hE hc
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) a] at h4
  omega

section Sporadic


theorem false_of_sporadic_rank_four {K S : Type} [Group K] [Finite K] [Group S] [Finite S]
    (hq : CFSG.IsQuasisimple K) (e : K ⧸ center K ≃* S) {s : TauCeti.SporadicName}
    (hs : s = .McL ∨ s = .Fi22 ∨ s = .Co1 ∨ s = .Co2 ∨ s = .Co3 ∨ s = .Ly ∨
      s = .B ∨ s = .HN ∨ s = .ONan ∨ s = .Fi24Prime) (hK : IsSporadic K s)
    {Y : Subgroup (MulAut S)} (hY : (MulAut.conj : S →* MulAut S).range ≤ Y)
    (hr : CFSG.Open.pRank 3 Y ≤ 3) : False := by
  obtain ⟨a⟩ := hK
  have : Finite (Carrier s) := Finite.of_equiv K a.toEquiv
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : IsSimpleGroup (Carrier .McL) := CFSG.Sporadic.McL.isSimpleGroup_McL
    exact false_of_rank_four_model hq e a CFSG.SectionRank.McL_elementary_three_rank_four hY hr
  · have : IsSimpleGroup (Carrier .Fi22) := CFSG.Sporadic.Fi22.isSimpleGroup_Fi22
    exact false_of_rank_four_model hq e a CFSG.SectionRank.Fi22_elementary_three_rank_four hY hr
  · have : IsSimpleGroup (Carrier .Co1) := CFSG.Sporadic.Co1.isSimpleGroup_Co1
    exact false_of_rank_four_model hq e a CFSG.SectionRank.Co1_elementary_three_rank_four hY hr
  · have : IsSimpleGroup (Carrier .Co2) := CFSG.Sporadic.Co2.isSimpleGroup_Co2
    exact false_of_rank_four_model hq e a CFSG.SectionRank.Co2_elementary_three_rank_four hY hr
  · have : IsSimpleGroup (Carrier .Co3) := CFSG.Sporadic.Co3.isSimpleGroup_Co3
    exact false_of_rank_four_model hq e a CFSG.SectionRank.Co3_elementary_three_rank_four hY hr
  · have : IsSimpleGroup (Carrier .Ly) := CFSG.Sporadic.Ly.isSimpleGroup_Ly
    exact false_of_rank_four_model hq e a CFSG.SectionRank.Ly_elementary_three_rank_four hY hr
  · have : IsSimpleGroup (Carrier .B) := CFSG.Sporadic.B.fam_b_simplicity
    exact false_of_rank_four_model hq e a CFSG.SectionRank.B_elementary_three_rank_four hY hr
  · have : IsSimpleGroup (Carrier .HN) := CFSG.Sporadic.HN.isSimpleGroup_HN
    exact false_of_rank_four_model hq e a CFSG.SectionRank.HN_elementary_three_rank_four hY hr
  · have : IsSimpleGroup (Carrier .ONan) := CFSG.Sporadic.ON.isSimpleGroup_ON
    exact false_of_rank_four_model hq e a CFSG.SectionRank.ON_elementary_three_rank_four hY hr
  · have : IsSimpleGroup (Carrier .Fi24Prime) := CFSG.Sporadic.Fi24.isSimpleGroup_Fi24prime
    exact false_of_rank_four_model hq e a CFSG.SectionRank.Fi24prime_elementary_three_rank_four hY hr

end Sporadic

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KbarListFive

end
