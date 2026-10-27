module

public import CFSG.ClassicalInvolution.RouteD.TWRExoticMain
public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootTwinCtx
public import CFSG.ClassicalInvolution.SmallCases.NDBCRes
import CFSG.ClassicalInvolution.SmallCases.NDBC0
import CFSG.ClassicalInvolution.Asc77.AscE187Img
import CFSG.ClassicalInvolution.Asc77.ModOApi
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
import CFSG.ClassicalInvolution.Balance.PassTwoModelFacts
public import CFSG.ClassicalInvolution.Asc77.AscBSCMain
public import CFSG.ClassicalInvolution.Asc77.AscBSD12
public import CFSG.ClassicalInvolution.Asc77.AscBSE8
import CFSG.ClassicalInvolution.Asc77.AscE187Cop
import CFSG.ClassicalInvolution.Asc77.AscThmABasic

public section

namespace CFSG.ClassicalInvolution.RouteD.TWR

set_option linter.unusedSectionVars false

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Disconnected
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => CFSG.ClassicalInvolution.Generic.CoreAssembly.conjClass

end CFSG.ClassicalInvolution.RouteD.TWR
