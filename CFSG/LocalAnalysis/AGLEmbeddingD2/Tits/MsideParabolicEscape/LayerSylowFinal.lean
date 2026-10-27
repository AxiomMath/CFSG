module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.LayerSylow
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.InvariantSylow

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

theorem invariantSylowStmt : InvariantSylowStmt := by
  intro M _ _ A S X hA hS hAS hXS hX2 hAX
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.InvariantSylow.exists_invariant_sylow_ge
    (p := 3) (q := 2) A S X hA hS hAS hXS hX2 hAX

theorem d2L34BetaLayerSylow_of_core (hinvH : D2L34BetaInvariantTwoInCore)
    (hCent : D2L34BetaLayerCentralized) : D2L34BetaLayerSylow :=
  d2L34BetaLayerSylow_of hinvH hCent invariantSylowStmt

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
