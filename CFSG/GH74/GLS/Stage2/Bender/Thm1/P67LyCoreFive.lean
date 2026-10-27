module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyCoreMain
public import CFSG.RankThree.PartOne.KS.LyFiveCore

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.LyCore

open Subgroup CFSG CFSG.Blueprint CFSG.RankThree.PartOne CFSG.RankThree.PartOne.LyFive

theorem lyCoreAt_five :
    LyCoreAt 5 := by
  intro Y _ _ hLy V hV hVc
  have := hV
  obtain ⟨eT⟩ := hLy
  let eJ : Y ≃* CFSG.Sporadic.Ly.J := eT.trans CFSG.Sporadic.Ly.lyEquivJ
  have hne : V ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hVc
    omega
  obtain ⟨⟨g, hgV⟩, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hg1' : g ≠ 1 := fun h => hg1 (Subtype.ext h)
  have hg5 : g ^ 5 = 1 := elemPow_eq_one_of_isElementaryAbelian g hgV
  have hord : orderOf g = 5 := orderOf_eq_prime hg5 hg1'
  refine ⟨g, hgV, hg1', ?_⟩
  intro W hWC hWn hcop
  have hJ : FiveCoreAt (eJ g) := fiveCore_J (eJ g) (by rw [MulEquiv.orderOf_eq]; exact hord)
  have h' : FiveCoreAt' g := by
    have := @fiveCoreAt'_map CFSG.Sporadic.Ly.J inferInstance Y _ eJ.symm (eJ g)
      (fiveCoreAt'_of_fiveCoreAt hJ)
    simpa using this
  refine eq_bot_of_fiveCoreAt' h' W hWC
    (fun c hc w hw => hWn c (mem_centralizer_singleton_iff.mp hc) w hw) ?_
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mp hcop.symm

theorem lyCentralizerCore_of_three
    (h3 : LyCoreAt 3) :
    LyCentralizerCore :=
  lyCentralizerCore_of_three_five h3 lyCoreAt_five

end CFSG.GH74.GLS.Stage2.Bender.Thm1.LyCore
