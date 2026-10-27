module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Open

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

structure SylCfg (Y : Type) [Group Y] (T W : Subgroup (MulAut Y)) : Prop where
  t2 : IsPGroup 2 ↥T
  w3 : IsPGroup 3 ↥W
  w_ne : W ≠ ⊥
  t_norm : T ≤ normalizer (W : Set (MulAut Y))
  syl : ∃ P : Subgroup (MulAut Y), P ≤ T ∧ P ≤ innSub Y ∧
    CFSG.ABGLocalTools.IsSylowOf 2 P (innSub Y)

@[expose] def SylCfgOf (Y : Type) [Group Y] : Prop := ∃ T W : Subgroup (MulAut Y), SylCfg Y T W

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
