module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.OrthL2.Main
public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.OrthL2.SixDim
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2 QuadraticMap
open CFSG.HardMathSupport.Lang.Coordinator.D4Bridge (Coord)

theorem leviSelfDual_of_blockLevi (K : Type) [Field K] [Finite K] : LeviSelfDual K :=
  fun _ hy _ hh hne1 hself hm =>
    specialBlock_eq_levi_selfDual (nondegenerate_quadPlus_four K) hy hh hne1 hself hm

theorem leviFixed_of_blockLevi (K : Type) [Field K] [Finite K] : LeviFixed K :=
  fun _ hy hK A B hAB hspan =>
    supportedFixedDerived_eq_levi (nondegenerate_quadPlus_four K) hy A B hAB hspan hK

theorem sixNotL2_of_sixDim (K : Type) [Field K] [Finite K] : SixNotL2 K :=
  fun R hR hd hK3 _ hr => not_isTypeL2_orthDerived_six R hR hd hK3 hr

section Wire

theorem d4RootSL2_holds : D4RootSL2 :=
  d4RootSL2_of_blocks CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
    (fun K _ _ => leviSelfDual_of_blockLevi K) (fun K _ _ => leviFixed_of_blockLevi K)
    (fun K _ _ => sixNotL2_of_sixDim K)

end Wire

end CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2
