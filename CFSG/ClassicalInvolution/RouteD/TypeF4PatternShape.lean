module

public import CFSG.ClassicalInvolution.RouteD.TypeF4PatternLayer
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpShape

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

variable {p f : ℕ} [Fact p.Prime]

@[expose] def F4PerpTableR (p f : ℕ) [Fact p.Prime] : Prop :=
  PerpTableR p f (F4Layer.rel (p := p) (f := f)) none .POmegaOdd 4

end CFSG.ClassicalInvolution.RouteD.NonClassical
