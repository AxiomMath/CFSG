module

public import CFSG.ClassicalInvolution.RouteD.TypeF4PatternPiece
public import CFSG.ClassicalInvolution.RouteD.TypeF4TwinModel
public import CFSG.ClassicalInvolution.RouteD.TypeF4TwinPerpTable
public import CFSG.ClassicalInvolution.Balance.Theorem5Boot

public section

namespace CFSG.ClassicalInvolution.Generic.CoreAssembly

open CFSG.ClassicalInvolution.RouteD.NonClassical
open CFSG.ClassicalInvolution.Balance.Theorem5 (TriangleLayers TriangleConnectedAll)

variable {p f : ℕ} [Fact p.Prime]

theorem sp3F4Side_of_twinP1 (hP1 : Sp3TwinP1 p f) : Sp3F4Side p f := by
  intro G _ _ _ hnab K z S hS hlink
  exact sp3F4Side_of_inputs hP1 (f4PerpTableR p f)
    (twinPartnerFactTwin_pOmegaOdd_four S.odd S.five) G hnab K z S hS hlink

end CFSG.ClassicalInvolution.Generic.CoreAssembly
