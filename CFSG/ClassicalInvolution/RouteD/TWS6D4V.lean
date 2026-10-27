module

public import CFSG.ClassicalInvolution.RouteD.TwinYR2SpinV
public import CFSG.ClassicalInvolution.RouteD.TwinYR2SpinNC
public import CFSG.ClassicalInvolution.Asc77.WP3SCSD4Gen
public import CFSG.ClassicalInvolution.Asc77.AscT7HS2
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpOrthLayer

public section

namespace CFSG.ClassicalInvolution.RouteD.TWS6

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Models.Transfer CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.Balance.StrongBalance.Orth
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open CFSG.ClassicalInvolution.Generic (Commutes conjSub mem_conjSub_iff conj_mem_conjSub)
open CFSG.ClassicalInvolution.ModelFacts (plusSp minusSp mem_plusSp mem_minusSp
  isCompl_plusSp_minusSp polar_plusSp_minusSp)
open scoped MatrixGroups commutatorElement

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

end CFSG.ClassicalInvolution.RouteD.TWS6
