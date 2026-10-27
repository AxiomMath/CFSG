module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineSevenA
import CFSG.LocalAnalysis.AGLEmbedding.EscapeTwoCore
import CFSG.LocalAnalysis.AGLEmbedding.CharCore
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Misc
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}

namespace NineCore

theorem pCoreOf_inf_mem_invTwoSubgroups (h : NineCore G M p Q H E k) :
    pCoreOf 2 (H ⊓ M) ∈ invTwoSubgroups H Q :=
  ⟨(pCoreOf_le 2 _).trans inf_le_left, pCoreOf_isPGroup 2 _,
    (le_inf h.Q_le_H h.Q_le_M).trans (localGroup_le_normalizer_pCoreOf 2 (H ⊓ M))⟩

theorem pCoreOf_two_le_inf (h : NineCore G M p Q H E k) :
    pCoreOf 2 H ≤ pCoreOf 2 (H ⊓ M) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have h1 : pCoreOf 2 H ≤ M :=
    (CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.pCoreOf_two_le_relPPrimeCore h.ne_two
      H).trans h.relPPrimeCore_le
  have h2 : pCoreOf 2 H ≤ H ⊓ M := le_inf (pCoreOf_le 2 H) h1
  exact normal_pGroup_le_pCoreOf 2 _ _ h2
    ((Subgroup.normal_subgroupOf_iff_le_normalizer h2).mpr
      (inf_le_left.trans (localGroup_le_normalizer_pCoreOf 2 H))) (pCoreOf_isPGroup 2 H)

theorem pCoreOf_inf_eq_of_le (h : NineCore G M p Q H E k)
    (hS : pCoreOf 2 (H ⊓ M) ≤ relPPrimeCore p H) : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H := by
  refine le_antisymm ?_ h.pCoreOf_two_le_inf
  set O : Subgroup G := relPPrimeCore p H with hO
  have hOH : O ≤ H := sSup_le fun _ hN => hN.1
  have hHO : H ≤ normalizer (O : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOH).mp
      (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
        h.prime H)
  have hOM : O ≤ H ⊓ M := le_inf hOH h.relPPrimeCore_le
  have hOS : O ≤ normalizer (pCoreOf 2 (H ⊓ M) : Set G) :=
    hOM.trans (localGroup_le_normalizer_pCoreOf 2 (H ⊓ M))
  have h1 : pCoreOf 2 (H ⊓ M) ≤ pCoreOf 2 O :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hS hOS (pCoreOf_isPGroup 2 _)
  have h2 : pCoreOf 2 O ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 O).trans hOH)
      (hHO.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 O))
      (pCoreOf_isPGroup 2 O)
  exact h1.trans h2

end NineCore

namespace NineSettingGen

theorem pCoreOf_inf_eq_of_le (h : NineSettingGen G M p Q H E k)
    (hS : pCoreOf 2 (H ⊓ M) ≤ relPPrimeCore p H) :
    pCoreOf 2 (H ⊓ M) = pCoreOf 2 H :=
  h.toCore.pCoreOf_inf_eq_of_le hS

end NineSettingGen

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
