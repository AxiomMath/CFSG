module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointCase2
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Unitary
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryInvolution
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryAutElemRank
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.M11Three

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem IsPPoint.false_three {P : Sylow 3 G} {M : Subgroup G} {x : G}
    (hin : PPointThreeInputs) (hS : D1Global G) (hD1 : D1For G) (hFC : FullCoreLocality G)
    (hInn : KFactInnerAction) (hWC : KFactWeakClosure) (h713 : GL83.I_7_13_1)
    (hloc : D1Local 3 P M) (h : IsPPoint 3 P M x) : False :=
  h.false_three_of_case2 hin hS hD1 hFC hInn hWC hloc fun hB =>
    h.conj_mem_sup_three hin hS hD1 hFC hInn hWC h713 hloc hB

theorem pElementPrimeFive_holds
    (h243 : GL83ComponentPCoreTrivial)
    (h244 : GL83NongenerationList) (hsig : GL83SignalizerAut)
    (h313 : GL83NormalElementaryRankFour) (hRB : KFactReeBorelMaximal)
    (hRI : KFactReeInvolution) (hInn : KFactInnerAction) (hWC : KFactWeakClosure)
    (h713 : GL83.I_7_13_1) : PElementPrimeFive G := by
  have hin : PPointThreeInputs :=
    ⟨h243, h244, hsig, h313, kFactUnitaryBorelMaximal, kFactUnitaryInvolution, hRB, hRI,
      kFactUnitaryAutElemRank, kFactM11Three⟩
  intro hS hD1 hFC p P M hloc x hx
  by_contra hlt
  have hp : p.Prime := hloc.beta.1
  have hp2 : p ≠ 2 := hloc.beta.2.1
  have hp3 : p = 3 := by
    have h5 : p < 5 := by omega
    have h2 : 2 ≤ p := hp.two_le
    interval_cases p
    · exact absurd rfl hp2
    · rfl
    · exact absurd hp (by norm_num)
  subst hp3
  obtain ⟨m, -, hpt⟩ := exists_isPPoint hFC hloc hx
  exact hpt.false_three hin hS hD1 hFC hInn hWC h713 hloc

end CFSG.LocalAnalysis.RankFourTheoremC
