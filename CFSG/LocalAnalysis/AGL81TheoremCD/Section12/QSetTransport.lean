module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.SylowQWlog
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8YCfgAct

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G] {M Q H : Subgroup G} {p : ℕ}

theorem exists_sylow_QSet_H4Star_of_twelveCtx
    (h : TwelveCtx G M p Q H)
    (hI : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineNineOneInput) :
    ∃ Q' : Subgroup G, Q ≤ Q' ∧ Q' ∈ CFSG.LocalAnalysis.RankThreeUC.AGL81C.QSet M p ∧
      CFSG.ABGLocalTools.IsSylowOf p Q' H ∧
      H ∈ CFSG.LocalAnalysis.RankThreeUC.AGL81C.H4StarFam p M Q' := by
  haveI : Fact p.Prime := ⟨h.p_prime⟩
  obtain ⟨P, hQP, hPset, hPH⟩ := exists_sylow_QSet_of_twelveCtx h hI
  have hH2Star : H ∈ H2StarFam M P :=
    CFSG.LocalAnalysis.AGL81TheoremCD.Section14.mem_H2StarFam_of_le h.H_mem_H2Star hPH.le
  have hCondA : CondA p M P H :=
    Or.inl (CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.YCfg.isSylowOf_inf_of_subnormalIn hPH
      (kSub_le p M H)
      (CFSG.LocalAnalysis.AGL81TheoremCD.Section14.kSub_subgroupOf_isSubnormal p M H))
  exact ⟨P, hQP, hPset, hPH, hH2Star, ⟨hH2Star.1, hCondA, h.H_mem_H4.2.2⟩⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
