module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinusCore
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinusReduce
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinusSmall
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinusTwo

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb

open CFSG.AGLEmbedding OmegaMinus

theorem twistedDFlagCell (hSQ : OmegaMinusSmallQS) (hSS : OmegaMinusSmallSplit) :
    TwistedDFlagCell := by
  intro r F _ _ _ b c hirr hr hK p hp57 S hS hA1 hA2 x hxΩ hxp hfix V E hVJ hVx hV hEV hEel hEc
  by_cases hpq : p ∣ Nat.card F - 1
  · exact false_of_split hirr hSQ hSS hr hp57 hK hpq hS hA1 hA2 hxΩ hxp hfix hVJ hVx hV hEV hEel
      hEc
  · exact false_of_nonsplit hirr hSQ hr hp57 hK hpq hS hA1 hxΩ hxp hfix hVJ hVx hV hEV hEel hEc

theorem altIbBarCell_twistedD_of_small (hSQ : OmegaMinusSmallQS) (hSS : OmegaMinusSmallSplit) :
    AltIbBarCell (IsLieOf IdxTwistedD) :=
  altIbBarCell_twistedD_of_flagCell (twistedDFlagCell hSQ hSS)

theorem omegaMinusSmallSplit : OmegaMinusSmallSplit :=
  fun F _ _ _ _ _ hirr p hp57 hpq =>
    ⟨orth_two_split hirr p hp57 hpq, omegaMinus_four_noAp hirr hp57 hpq⟩

theorem altIbBarCell_twistedD : AltIbBarCell (IsLieOf IdxTwistedD) :=
  altIbBarCell_twistedD_of_small omegaMinusSmallQS omegaMinusSmallSplit

theorem altIbCell_twistedD (hSch : KFactCatalogSchreier)
    (hGA : CFSG.Open.GriessAllModelsStatement) : AltIbCell (IsLieOf IdxTwistedD) :=
  altIbCell_of_barCell hSch hGA (fun _ _ hX => Or.inr (Or.inr (Or.inl hX))) altIbBarCell_twistedD

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb
