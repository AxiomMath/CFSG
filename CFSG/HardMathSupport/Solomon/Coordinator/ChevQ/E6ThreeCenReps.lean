module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeModel

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.StandardType.TableBExc.E6Three (gE6 cE6)

@[expose] def e6CenZ : WeylGroup Tag.E6 := gE6 0 * gE6 1 * gE6 2

@[expose] def e6CenO1 : Subgroup (WeylGroup Tag.E6) := Subgroup.zpowers e6CenZ

@[expose] def e6CenOA : Subgroup (WeylGroup Tag.E6) := Subgroup.closure {gE6 0, gE6 1 * gE6 2}

@[expose] def e6CenOB : Subgroup (WeylGroup Tag.E6) :=
  Subgroup.closure {gE6 0 * gE6 1 ^ 2, gE6 1 * gE6 2 ^ 2}

@[expose] def e6CenOT : Subgroup (WeylGroup Tag.E6) := Subgroup.closure {cE6, e6CenZ}

@[expose] def e6CenO3 : Subgroup (WeylGroup Tag.E6) := Subgroup.closure {gE6 0, gE6 1, gE6 2}

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
