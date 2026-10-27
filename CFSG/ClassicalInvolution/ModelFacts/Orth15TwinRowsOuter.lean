module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinRows
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterL4Model
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterU4Model
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterSp4Model

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.ModelFacts.Orth15

variable (p : ℕ) [Fact p.Prime]

theorem twinSmallOuterSp : TwinSmallOuterSp p := fun hp2 _ hq hadm =>
  twinOuterAlpha_psp2 hp2 hq hadm

theorem twinSmallOuterSL : TwinSmallOuterSL p := fun hp2 _ _ hadm =>
  twinOuterAlpha_psl4 hp2 hadm

theorem twinSmallOuterSU : TwinSmallOuterSU p := fun hp2 _ hq hadm =>
  twinOuterAlpha_psu4 hp2 hq hadm

variable {p}

theorem twinSmallOuter_of_d4 (hd4 : TwinSmallOuterD4 p) : TwinSmallOuter p :=
  twinSmallOuter_of_rows (twinSmallOuterSp p) (twinSmallOuterSL p) (twinSmallOuterSU p) hd4

end CFSG.ClassicalInvolution.Asc77
