module

public import CFSG.CGT.Foote82.T66.Basic
public import CFSG.CGT.Foote82.T66.CitedL13
import CFSG.CGT.Foote82.T66.FaithfulImage
import CFSG.CGT.Foote82.T66.FaithfulAlt

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem faithfulTildeV_of_isFPrimeModule (hU42 : H1OmegaMinusSix) (hO8 : H1OmegaMinusEight)
    (hA7 : H1AltSevenFour) (hA6 : H1ThreeAltSix) {L : Subgroup (GLV V)}
    (hq : CFSG.Open.IsQuasisimple ↥L) (hirr : HasIrrTildeV L) (hf : IsFPrimeModule L) :
    FaithfulTildeV L := by
  rcases hf with ⟨n, hn, h⟩ | h | h | h | h | h
  · exact L13Aux.faithfulTildeV_of_alt hq hirr hn h
  · exact L13Aux.faithfulTildeV_of_a7Four hA7 hq hirr h
  · exact L13Aux.faithfulTildeV_of_alt hq hirr (by norm_num)
      (L13Aux.isAltNaturalModule_of_omegaPlus_three h)
  · exact L13Aux.faithfulTildeV_of_omegaMinus hq hirr h hU42
  · exact L13Aux.faithfulTildeV_of_omegaMinus hq hirr h hO8
  · exact L13Aux.faithfulTildeV_of_a6Z3 hA6 hq hirr h

theorem thm66FNonFaith_holds (hU42 : H1OmegaMinusSix) (hO8 : H1OmegaMinusEight)
    (hA7 : H1AltSevenFour) (hA6 : H1ThreeAltSix) : Thm66FNonFaith := by
  intro V _ _ _ G S L hc hnf
  exact (hnf (faithfulTildeV_of_isFPrimeModule hU42 hO8 hA7 hA6 hc.setup.component.2.2
    hc.setup.irrTilde hc.fmod)).elim

end CFSG.CGT.Foote82
