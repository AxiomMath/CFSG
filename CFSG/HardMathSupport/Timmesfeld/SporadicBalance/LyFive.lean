module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OuterTrivial
public import CFSG.RankThree.PartOne.KS.LyFiveCore

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.Proving CFSG.RankThree.PartOne

theorem oPrimeCoreTrivialAt_Ly_five
    (S : Type) [Group S] [Finite S] (hS : Nonempty (S ≃* NativeSporadic.Carrier .Ly)) :
    OPrimeCoreTrivialAt 5 S := by
  obtain ⟨eT⟩ := hS
  let eJ : S ≃* CFSG.Sporadic.Ly.J := eT.trans CFSG.Sporadic.Ly.lyEquivJ
  intro g hg
  have hJ : FiveCoreAt (eJ g) :=
    LyFive.fiveCore_J (eJ g) (by rw [MulEquiv.orderOf_eq]; exact hg)
  have h' : FiveCoreAt' g := by
    have := @fiveCoreAt'_map CFSG.Sporadic.Ly.J inferInstance S _ eJ.symm (eJ g)
      (fiveCoreAt'_of_fiveCoreAt hJ)
    rwa [MulEquiv.symm_apply_apply] at this
  exact eq_bot_of_fiveCoreAt' h' _ (GLAPPrimeCoreOf_le _)
    (fun c hc w hw => GLAPPrimeCoreOf_conj_mem c hc w hw)
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mp
      (coprime_card_GLAPPrimeCoreOf Nat.prime_five _))

theorem sporadicOPrimeHolds_Ly_five :
    SporadicOPrimeHolds .Ly 5 :=
  fun S _ _ _ hS => oPrimeCoreTrivialAt_Ly_five S hS

theorem sporadicOnePairHolds_Ly_five :
    SporadicOnePairHolds .Ly 5 :=
  ⟨sporadicOPrimeHolds_Ly_five, sporadicOuterHolds_Ly 5⟩

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
