module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BrBridge
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Lift55
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Count55

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem bridge55_thm (hS : P34.GHSchreier) (hL31 : Lemma31Narrow) (hInv : InvSec) : Bridge55 :=
  bridge55_of hS lift55_thm (count55_of hL31) hInv

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
