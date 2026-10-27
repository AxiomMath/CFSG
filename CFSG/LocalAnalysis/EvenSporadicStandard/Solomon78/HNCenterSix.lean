module

public import CFSG.RankThree.PartOne.S11c.HNInvQ6
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.CenterAt
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Closing
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore CFSG.RankThree.PartOne.HNRed

theorem centerInvAt_aJ :
    CenterInvAt aJ := by
  intro z _ hzc
  let zC : C6 := ⟨z, Subgroup.mem_centralizer_singleton_iff.2 (hzc aJ rfl)⟩
  have h1 : phi6 zC = 1 := by
    refine centralizer_Dsub_trivial fun d hd => ?_
    obtain ⟨y, rfl⟩ := Dsub_le_range hd
    rw [← map_mul, ← map_mul]
    exact congrArg phi6 (Subtype.ext (hzc y (Subgroup.mem_centralizer_singleton_iff.1 y.2)))
  rcases eq_one_or_eq_of_card_two phi6.ker card_ker_phi6 t6C_mem_ker t6C_ne_one
    (MonoidHom.mem_ker.2 h1) with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val h)

end CFSG.EvenSporadicStandard.Solomon78
