module

public import CFSG.LieType.ChevTwo.OppositeFixedExcF4
public import CFSG.LieType.ChevTwo.OppositeFixedExcBender
public import CFSG.LieType.ChevTwo.OppositeFixedExcTri
public import CFSG.LieType.ChevTwo.OppositeFixedExcTwE6
public import CFSG.LieType.ChevTwo.OppositeFixedExcReeFinal
public import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel

public section

namespace CFSG.LieType.ChevTwo

open CFSG.Blueprint CFSG.Blueprint.Chevalley TauCeti CFSG.StandardType.ChevTwo
  CFSG.LieType.ChevTwo.Semi


theorem oppositeFixed_of_isChevTwoExc_cert {S : Type} [Group S] [Finite S] (h : IsChevTwoExc S) :
    OppositeFixed S := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := h
  have hB := CFSG.TauCetiBridge.Even.chevalleyBridgesAll
  cases d with
  | A r q => exact hd.elim
  | twistedA r q => exact hd.elim
  | B r q => exact hd.elim
  | C r q => exact hd.elim
  | D r q => exact hd.elim
  | twistedD r q => exact hd.elim
  | G2 q => exact hd.elim
  | reeG2 m => exact hd.elim
  | E6 q =>
    have hp : q.p = 2 := hd
    exact oppositeFixed_of_untwistedChevalleyModel_E6 q.exponent_pos
      (untwistedChevalleyModel_of_bridge hB.e6 q hv hp e)
  | E7 q =>
    have hp : q.p = 2 := hd
    exact oppositeFixed_of_untwistedChevalleyModel_E78 (Or.inl rfl) q.exponent_pos
      (untwistedChevalleyModel_of_bridge hB.e7 q hv hp e)
  | E8 q =>
    have hp : q.p = 2 := hd
    exact oppositeFixed_of_untwistedChevalleyModel_E78 (Or.inr rfl) q.exponent_pos
      (untwistedChevalleyModel_of_bridge hB.e8 q hv hp e)
  | F4 q =>
    have hp : q.p = 2 := hd
    exact oppositeFixed_of_untwistedChevalleyModel_F4 q.exponent_pos
      (untwistedChevalleyModel_of_bridge hB.f4 q hv hp e)
  | twistedE6 q =>
    have hp : q.p = 2 := hd
    exact oppositeFixed_of_twistedChevalleyModel_E6 q.exponent_pos
      (twistedChevalleyModel_of_bridge hB.twistedE6 q hv hp e)
  | trialityD4 q =>
    have hp : q.p = 2 := hd
    exact oppositeFixed_of_twistedChevalleyModel_D4 q.exponent_pos
      (twistedChevalleyModel_of_bridge hB.trialityD4 q hv hp e)
  | suzuki m => exact oppositeFixed_of_valid_suzuki m hv e
  | reeF4 a =>
    have ha : 1 ≤ a := (LieTypeIndex.inStandardRange_iff _).mp
      ((LieTypeIndex.valid_iff _).mp hv).1
    exact oppositeFixed_of_reeTitsModel_twistedF4 ha (reeTitsModel_of_reeF4 a hv e)
  | tits => exact oppositeFixed_of_titsModel_cert (reeTitsModel_of_tits hv e)

end CFSG.LieType.ChevTwo
