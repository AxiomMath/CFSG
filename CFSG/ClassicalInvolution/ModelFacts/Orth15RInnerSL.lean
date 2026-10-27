module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinRows
public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerL4Model

public section

namespace CFSG.ClassicalInvolution.Asc77

variable (p : ℕ) [Fact p.Prime]

theorem twinSmallInnerSL : TwinSmallInnerSL p := fun hp2 _ hq hadm =>
  ModelFacts.Orth15.twinInnerAlpha_psl4 hp2 hq hadm

end CFSG.ClassicalInvolution.Asc77
