module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Split.SplitPair
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.Glue
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd.Glue
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd.Shintani
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd.ThreeD4
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd.G2Class

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph


theorem d4GraphA2PairGen_of_nonsplit (h : D4GraphA2PairGenNonsplit) : D4GraphA2PairGen :=
  d4GraphA2PairGen_of_split d4GraphA2PairGenSplit_holds h

theorem d4GraphPairGen_of_nonsplit (h : D4GraphA2PairGenNonsplit) : D4GraphPairGen :=
  d4GraphPairGen_of (ClassOdd.d4GraphClassOdd_of
      (ClassOdd.graphShintaniNF_of ClassOdd.threeD4FixedNF_holds) ClassOdd.g2ThreeClass_holds) (d4GraphA2PairGen_of_nonsplit h)

theorem d4ThreeGraphPlanesEven_of_nonsplit (h : D4GraphA2PairGenNonsplit)
    (h2 : D4GraphPlanesTwo) : D4ThreeGraphPlanesEven :=
  d4ThreeGraphPlanesEven_of_open (d4GraphA2PairGen_of_nonsplit h) h2

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
