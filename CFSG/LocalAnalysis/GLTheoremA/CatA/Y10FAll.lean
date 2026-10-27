module

public import CFSG.LocalAnalysis.GLTheoremA.S11.YS10Cat6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSeitzRest
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FU64Final
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FU6Rank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10F165
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10F166

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

structure Y10Facts : Prop where
  i165 : I165Fact
  seitzRest : SeitzCubeRest
  seitzEvenCentre : SeitzEvenCentre
  i166 : I166Fact
  i1441 : I1441FactS
  i14neg : I14NegFactS
  u64 : U64FactS
  u6mem : U6Mem
  u6cent : U6Cent

section Certs


theorem s11Cat6Inputs_of_facts (h : Y10Facts) {G : Type} [Group G] [Finite G] : S11Cat6Inputs G :=
  { i165 := i165At_of_facts h.i165
    i2315a := i2315aAt_of_facts h.seitzRest h.seitzEvenCentre
    i2315b := i2315bAt_of_facts h.seitzRest
    i166 := i166At_of_facts h.i166
    i1441 := i1441At_of_facts h.i1441
    i14neg := i14NegAt_of_facts h.i14neg
    u64types := u64TypesAt_of_facts h.u64
    u6struct := u6StructAt_of_facts h.u6mem h.u6cent }

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F
