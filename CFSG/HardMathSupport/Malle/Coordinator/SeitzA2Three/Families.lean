module

public import CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three.AssemblyU
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.PSLnL4
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieOffCharOuterCubeUnitary

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three

open CFSG.AGLEmbedding

theorem kFactSeitzOuterCubeRankTwoAt_A_of_pieces
    {m : ℕ} (hm : 1 ≤ m) {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.A m q).Valid)
    (hNF : A2ThreeNormalForm) (hH : A2ThreeHeisGen) (h64 : A2ThreeSixtyFour) :
    KFactSeitzOuterCubeRankTwoAt ⟨.A m q, hv⟩ :=
  kFactSeitzOuterCubeRankTwoAt_of_atPrime fun p _ => by
    by_cases hexc : m = 2 ∧ p = 3 ∧ 3 ∣ q.card - 1
    · obtain ⟨rfl, rfl, h3⟩ := hexc
      exact kFactSeitzOuterCubeRankTwoAtPrime_A2_three_of_pieces hv h3 hNF hH h64
    · exact CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.kFactSeitzOuterCubeRankTwoAtPrime_A_final
        hm hv hexc

theorem kFactSeitzOuterCubeRankTwoAt_twistedA_of_pieces {m : ℕ}
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedA m q).Valid)
    (hNF : U3ThreeNormalForm) (hH : U3ThreeHeisGen) :
    KFactSeitzOuterCubeRankTwoAt ⟨.twistedA m q, hv⟩ :=
  kFactSeitzOuterCubeRankTwoAt_of_atPrime fun p _ => by
    by_cases hex : p = 3 ∧ m = 2 ∧ 3 ∣ q.card + 1
    · obtain ⟨rfl, rfl, h3⟩ := hex
      exact kFactSeitzOuterCubeRankTwoAtPrime_U3_three_of_pieces hv h3 hNF hH
    · exact kFactSeitzOuterCubeRankTwoAtPrime_twistedA hv hex

end CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three
