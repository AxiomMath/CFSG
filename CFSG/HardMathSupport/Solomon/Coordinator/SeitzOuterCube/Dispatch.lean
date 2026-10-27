module

public import CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three.Families
import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.OuterCubeOrthogonal
import CFSG.HardMathSupport.Malle.Proving.A2ThreeSixtyFour
import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Vacuous
import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.OrthFixedLeDerivedProof
import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3NormalFormProof
import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3Heis.Main
import CFSG.LieType.SeitzGeneration.OmegaF2.Plus
import CFSG.LieType.SeitzGeneration.OmegaF2.Minus
import CFSG.LieType.SeitzGeneration.RootPairOrthOmega

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube

open CFSG.AGLEmbedding CFSG.LieType.SeitzGeneration
open CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three
open CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter

@[expose] def KFactSeitzOuterCubeRankTwoExcRest : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, ¬ IsClassicalIndex d.1 → (∀ m, d.1 ≠ .suzuki m) →
    (∀ m, d.1 ≠ .reeG2 m) → d.1 ≠ .tits → KFactSeitzOuterCubeRankTwoAt d

section Dispatch


theorem kFactSeitzOuterCubeRankTwo_of_residuals (hHU : U3ThreeHeisGen)
    (hExc : KFactSeitzOuterCubeRankTwoExcRest) : KFactSeitzOuterCubeRankTwo :=
  kFactSeitzOuterCubeRankTwo_of_at fun ⟨d, hv⟩ => by
    have hrange : d.InStandardRange := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    by_cases hcl : IsClassicalIndex d
    · rcases (isClassicalIndex_iff hrange).1 hcl with ⟨m, q, rfl⟩ | ⟨m, q, rfl⟩ | hsym | horth
      · exact kFactSeitzOuterCubeRankTwoAt_A_of_pieces
          ((TauCeti.LieTypeIndex.inStandardRange_iff _).1 hrange).1 hv a2ThreeNormalForm_holds
          A2Heis.a2ThreeHeisGen_holds a2ThreeSixtyFour_holds
      · exact kFactSeitzOuterCubeRankTwoAt_twistedA_of_pieces hv u3ThreeNormalForm_holds hHU
      · exact kFactSeitzOuterCubeRankTwoAt_of_atPrime fun _ _ =>
          kFactSeitzOuterCubeRankTwoAtPrime_symplectic hsym
      · exact kFactSeitzOuterCubeRankTwoAt_of_atPrime fun _ _ =>
          kFactSeitzOuterCubeRankTwoAtPrime_orthogonal (subfieldPairOmega_of_char2
              (subfieldPairOmegaPlusChar2_of_F2 subfieldPairOmegaPlusF2_holds)
              (subfieldPairOmegaMinusChar2_of_F2 subfieldPairOmegaMinusF2_holds))
            orthFixedLeDerivedAll_holds horth
    · by_cases hs : ∃ m, d = .suzuki m
      · obtain ⟨m, rfl⟩ := hs
        exact kFactSeitzOuterCubeRankTwoAt_suzuki hv
      by_cases hr : ∃ m, d = .reeG2 m
      · obtain ⟨m, rfl⟩ := hr
        exact kFactSeitzOuterCubeRankTwoAt_reeG2 hv
      by_cases ht : d = .tits
      · subst ht
        exact kFactSeitzOuterCubeRankTwoAt_tits hv
      exact hExc ⟨d, hv⟩ hcl (fun m h => hs ⟨m, h⟩) (fun m h => hr ⟨m, h⟩) ht

theorem kFactSeitzOuterCubeRankTwo_of_excRest (hExc : KFactSeitzOuterCubeRankTwoExcRest) :
    KFactSeitzOuterCubeRankTwo :=
  kFactSeitzOuterCubeRankTwo_of_residuals U3Heis.u3ThreeHeisGen_holds hExc

end Dispatch

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube
