module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ReducedLayer
public import CFSG.Adapters.QiuzhenLegacy.FeitThompson.Gorenstein.RelativeZJ

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.RankThreeCoreUniqueness.Helpers

theorem hasPrimeConstraint_of_isPConstrained {p : ℕ} [Fact p.Prime] {H : Type*} [Group H]
    [Finite H] (h : CFSG.ABGLocalTools.IsPConstrained p H) : HasPrimeConstraint (G := H) p :=
  ⟨CFSG.pCore p (H ⧸ primeComplementCore (G := H) p), CFSG.pCore_normal, CFSG.pCore_isPGroup,
    CFSG.ABGTheoremB.RelativeZJ.centralizer_pCore_quotient_le h⟩

theorem isPConstrained_iff_hasPrimeConstraint {p : ℕ} [Fact p.Prime] {H : Type*} [Group H]
    [Finite H] : CFSG.ABGLocalTools.IsPConstrained p H ↔ HasPrimeConstraint (G := H) p :=
  ⟨hasPrimeConstraint_of_isPConstrained, isPConstrained_of_hasPrimeConstraint⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
