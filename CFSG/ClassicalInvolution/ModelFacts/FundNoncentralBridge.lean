module

public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralMain
public import CFSG.ClassicalInvolution.RouteD.GapsLocal

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

theorem fundNoncentral (p : ℕ) [Fact p.Prime] : FundNoncentral p :=
  fun t n e hft hadm hne R hR r hrR hr =>
    CFSG.ClassicalInvolution.ModelFacts.fundNoncentral_generic p t n e hft hadm hne R hR r hrR hr

end CFSG.ClassicalInvolution.RouteD.Gaps
