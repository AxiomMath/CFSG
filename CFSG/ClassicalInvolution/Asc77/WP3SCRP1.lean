module

public import CFSG.ClassicalInvolution.Asc77.WP3SCRP1Base
public import CFSG.ClassicalInvolution.Asc77.WP3SCRBoot
public import CFSG.ClassicalInvolution.RouteD.SCRTwinGenSL4
public import CFSG.ClassicalInvolution.RouteD.SCRTwinGenSp4
public import CFSG.ClassicalInvolution.RouteD.SCRTwinGenSu4
public import CFSG.ClassicalInvolution.RouteD.G2D4Ih8Free
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterU4Model
public import CFSG.Timmesfeld.ARS.CaseEFrame
public import CFSG.Timmesfeld.ARS.CaseMLevi
public import CFSG.Timmesfeld.ARS.Sec12Center
public import CFSG.Timmesfeld.ARS.Sec13Closed
public import CFSG.Timmesfeld.ARS.Sec13Maximal
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD.TwinY

section Rows

variable {p f : ℕ} [Fact p.Prime]

local notation "LTag" => CFSG.Assembly.LowTwoRank.StatedLieTag

end Rows

end CFSG.ClassicalInvolution.Asc77
