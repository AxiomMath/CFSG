module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32NonabFB2
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2Core1Out
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Abstract
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupSz32SigOne
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PointConfig
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIICommon
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PSU3.Aut
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.RankThree.PartOne.Census3 (IsoLie)

section Part

variable {Y : Type} [Group Y] [Finite Y] {F Γ B R₀ : Subgroup Y} {x : Y} {L : Subgroup Y} {z : Y}

theorem nf5_F_not_le (h9 : KFactNoM125Sylow') (hc : NF5Cfg F Γ B R₀ x L z) : ¬ F ≤ L := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  intro hFL
  have h : NF5 F Γ B R₀ x := hc.data
  obtain ⟨hsimple, hnon, hcat⟩ := szh1_simple_data h.catalog hc.comp hc.cen
  have hP5 := CFSG.ABGLocalTools.isSylowOf_iff.mp h.sylow
  have hndvd : ¬ 5 ∣ F.index := by
    have h5 := hP5.2.2
    rwa [Subgroup.relIndex_top_right] at h5
  have hsyl : CFSG.ABGLocalTools.IsSylowOf 5 F L := by
    refine CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hFL, hP5.2.1, fun hdvd => hndvd ?_⟩
    rw [← Subgroup.relIndex_mul_index hFL]
    exact Dvd.dvd.mul_right hdvd _
  obtain ⟨S, hS⟩ := hsyl.exists_sylow_eq_subgroupOf
  have hnonS : ¬ IsMulCommutative ↥(F.subgroupOf L) := by
    intro hcomm
    apply h.nonab
    rw [isMulCommutative_iff] at hcomm ⊢
    intro a b
    have e := Subgroup.subgroupOfEquivOfLe hFL
    have hab := hcomm (e.symm a) (e.symm b)
    have := congrArg e hab
    simpa using this
  have hs5 : ∃ s ∈ F, s ^ 5 ≠ 1 := by
    by_contra hne
    push_neg at hne
    have hBF : B = F := by
      ext b
      rw [h.hB b]
      exact ⟨fun hb => hb.1, fun hb => ⟨hb, hne b hb⟩⟩
    have hcard := h.Bcard
    rw [hBF, h.card] at hcard
    norm_num at hcard
  have hS' : (S : Subgroup L) = F.subgroupOf L := hS
  refine h9 ↥L hsimple hnon hcat S ?_
  rw [hS']
  refine ⟨?_, hnonS, ?_, ?_⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFL).toEquiv, h.card]
  · intro s hs
    have hsF : (s : Y) ∈ F := Subgroup.mem_subgroupOf.mp hs
    apply Subtype.ext
    simpa using h.exp _ hsF
  · obtain ⟨s, hsF, hs5'⟩ := hs5
    refine ⟨⟨s, hFL hsF⟩, Subgroup.mem_subgroupOf.mpr hsF, ?_⟩
    intro h'
    apply hs5'
    simpa using congrArg Subtype.val h'

end Part

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
