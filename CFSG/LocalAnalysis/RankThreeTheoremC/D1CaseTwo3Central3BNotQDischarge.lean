module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BNotQDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BNotQDischargeNineThree
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BInnerQShape
import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111B3
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3ReducedA
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open Hyp111

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)} {z : H}
  {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} {E : Subgroup G}

theorem InnerNotQConfig.le_X0_of_ne (hC : InnerNotQConfig p P M H R Rbar z L E)
    {L' : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL' : IsComponentOf L' ⊤)
    (hne : L ≠ L') : L' ≤ d1X0 p M H := by
  by_contra hL'X
  exact InnerQ.not_gamma_le_of_two_components hC.cfg.ext.prime hC.isComponent hL' hne hL'X
    hC.fieldOmega.2.1 hC.fieldOmega.2.2.2.1 hC.gamma

theorem InnerNotQConfig.nineThree (hOut : KFactOutCyclic)
    (hC : InnerNotQConfig p P M H R Rbar z L E) : Hyp111NineThree p M H L :=
  (⟨hC.cfg, hC.cyclic⟩ : D1CaseTwoDataU p P M H R Rbar).nineThree_of_forall_le
    (hC.cfg.red.cycAutRankLeTwo_of_kFactOutCyclic hC.cfg.catalog hOut) hC.isComponent hC.not_le
    fun _ hL' hne => hC.le_X0_of_ne hL' hne

theorem InnerNotQConfig.innerNotQJ_eq (hOut : KFactOutCyclic)
    (hC : InnerNotQConfig p P M H R Rbar z L E) : innerNotQJ p H L = L := by
  haveI := (hC.nineThree hOut).normal
  exact innerNotQJ_eq_of_normal p H L

theorem InnerNotQConfig.b3 (hOut : KFactOutCyclic) (hS : KFactSeitzCyc) (hNo2 : KFactCaseTwoNoTwo)
    (hC : InnerNotQConfig p P M H R Rbar z L E) : Hyp111B3 p H E (innerNotQJ p H L) := by
  haveI := (hC.nineThree hOut).normal
  have hcase : IsCaseTwoGroup p L :=
    hC.cfg.red.isCaseTwoGroup_of_not_le3 hC.cfg.catalog hOut hS hC.cyclic
      hC.cfg.pRank_rbar_eq_three hC.isComponent hC.not_le
  rw [innerNotQJ_eq_of_normal]
  exact b3_of_isFieldOmegaA hNo2 hC.cfg.ext.prime hcase hC.fieldOmega

theorem innerNotQNineThree_of_out (hOut : KFactOutCyclic) : InnerNotQNineThree G := by
  intro p P M H R Rbar z L E hC
  have h93 := hC.nineThree hOut
  rwa [hC.innerNotQJ_eq hOut]

end CFSG.LocalAnalysis.RankThreeTheoremC
