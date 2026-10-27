module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.OddFix
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.CoverFours
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HSData

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.card_sylow_dvd_four_twoHS
    {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : StdHyp G L) (hZ : Nat.card (center L) = 2) (hq : IsSporadic (L ⧸ center L) .HS)
    (S : Sylow 2 (centralizer (L : Set G))) : Nat.card S ∣ 4 := by
  have : Group.IsPerfect L := Group.isPerfect_def.2 h.standard.1.1
  have hexp : ∀ c ∈ center L, c ^ 2 = 1 := by
    intro c hc
    have h2 : orderOf (⟨c, hc⟩ : center L) ∣ 2 := hZ ▸ orderOf_dvd_natCard _
    simpa using congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.1 h2)
  exact h.card_sylow_dvd_four_of_facts hexp (index_dvd_two_of_isSporadic_hs hq)
    (oddFixFourth_of_isSporadic_hs hq) (foursGroupCondition_of_isSporadic_cover_hs hZ hq) S

end CFSG.EvenSporadicStandard.TwoHS
