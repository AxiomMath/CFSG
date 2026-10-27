module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23Socle
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23EqON
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23Suz
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23L316
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23Ne
public import CFSG.Sporadic.Recognition.HeMultiplierCert

public section

namespace CFSG.ComponentClassification.GSThmB.CF23L34

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.CatFactsL4U4
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.CatFactsL4U4.OutInv

theorem cf23L34Step_of_inputs
    (hS : CF23L34Socle) (hSM : SporadicMultTwoPartInput) (hHe : CF23L34HeStep) :
    CF23L34Step := by
  intro H _ _ h hT hL
  by_cases hKa : conjugate h.K h.a = h.K
  · rcases socle_cases hKa hS hL with (hHeN | ⟨hαN, hSuz | hON⟩) | ⟨hN, hcos⟩
    · obtain ⟨e⟩ := hHeN
      obtain ⟨eN⟩ := nonempty_NL_equiv hKa
      have hZK : center (OddBar h.K) = ⊥ :=
        Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate (OddBar h.K)
          h.isQuasisimple_K ⟨eN.symm.trans e⟩
      exact hHe H h hT hL hKa ⟨(QuotientGroup.quotientBot.symm.trans
        (QuotientGroup.quotientMulEquivOfEq hZK.symm)).trans (eN.symm.trans e)⟩
    · exact fus23ConclW_of_Suz hKa hT hL hαN hSuz
    · exact fus23ConclW_of_ON hKa hL hSM hαN hON
    · exact fus23ConclW_of_L316 hKa hL hN hcos
  · exact fus23ConclW_of_ne h hKa hL

end CFSG.ComponentClassification.GSThmB.CF23L34
