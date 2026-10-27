module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BNotQDischarge
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111OneSmallKappa

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers Hyp111

variable {G : Type} [Group G] [Finite G]

theorem InnerNotQConfig.d1Kappa_eq_card_innerNotQJ (hOut : KFactOutCyclic) {p : ℕ}
    {P : Sylow p G} {M H R : Subgroup G} {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    {z : H} {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} {E : Subgroup G}
    (hC : InnerNotQConfig p P M H R Rbar z L E) :
    d1Kappa p M H = Nat.card (innerNotQJ p H L) := by
  unfold d1Kappa
  rw [hC.innerNotQJ_eq hOut, d1KBar_eq_of_unique hC.isComponent hC.not_le fun L' hL' hL'X => by
    by_contra hne
    exact hL'X (hC.le_X0_of_ne hL' (Ne.symm hne))]

end CFSG.LocalAnalysis.RankThreeTheoremC
