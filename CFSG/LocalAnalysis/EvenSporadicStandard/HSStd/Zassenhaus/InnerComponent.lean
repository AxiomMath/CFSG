module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.FS79Thm13Guarded
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Thm38
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.StdBareStandard

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
  CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78

theorem standardComponentIsStandard_of_stdBare {H : Type} [Group H] [Finite H] {M : Subgroup H}
    {x : H} (hx : orderOf x = 2) (hM : IsCompIn M (centralizer ({x} : Set H)))
    (hstd : StdBare M) : standardComponentIsStandard M :=
  standardComponentIsStandard_of_stdBare'
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff ↥M).2.2.1.1 hM.isQuasisimple)
    (even_card_centralizer_of_le_centralizer hx hM.le) hstd

theorem false_of_maximalF_hs {G : Type} [Group G] [Finite G] (h13 : FS79Thm13UseSec G)
    (h38 : ComponentClassification.RankTwoSporadic.SporadicCaseOdd .HS) {L : Subgroup G}
    (hStd : StdHyp G L) {M : Subgroup G} (hmax : MaximalF M)
    (hq : IsSporadic (M ⧸ center M) .HS) (hrkM : CFSG.pRank 2 ↥M ≠ 1)
    (hrk : 2 ≤ Open.pRank 2 (centralizer (M : Set G))) : False := by
  obtain ⟨x, hx, hxM⟩ := hmax.1
  have hstd : StdBare M := h13.at hStd.kProper ⊤ hStd.fStarSimple (fun _ _ => le_top) M hmax hrkM
  exact hs_standard_rank_two_false h38 hStd (standardComponentIsStandard_of_stdBare hx hxM hstd)
    hq hrk

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
