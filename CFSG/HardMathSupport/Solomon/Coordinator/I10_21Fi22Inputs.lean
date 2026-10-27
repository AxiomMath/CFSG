module

public import CFSG.Sporadic.GLQ.RegisterProgram
public meta import CFSG.Sporadic.GLQ.RegisterProgram
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public meta import Certificates.Data.CFSGNative.SectionRank.F3
import CFSG.Blueprint.NativeSporadic
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public meta import CFSG.Open.Defs
public import CFSG.Open.Defs

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint CFSG.Sporadic.GLQ
open CFSG.F3.Native (V)

@[expose] def i1021Fi22Conj : Fin 5 → List ℤ :=
  ![[], [2, 2, 1, 2], [2, 2, 2, 1, 2, 1, 2], [2, 2, 2, 2, 1, 2, 2, 2, 2, 2],
    [2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2]]

@[expose] def i1021Fi22Word (j : Fin 5) : List ℤ :=
  i1021Fi22Conj j ++ [1] ++ (i1021Fi22Conj j).reverse.map fun l => -l

@[expose] def i1021Fi22RegA : Array V × Array V :=
  ((ops3 77).decode NativeSporadic.Fi22Seed1, (ops3 77).decode NativeSporadic.Fi22Seed1)

@[expose] def i1021Fi22RegB : Array V × Array V :=
  ((ops3 77).decode NativeSporadic.Fi22Seed2,
    (ops3 77).pow ((ops3 77).decode NativeSporadic.Fi22Seed2) 12)

@[expose] def i1021Fi22X (j : Fin 5) : Array V :=
  signedWordN (ops3 77) i1021Fi22RegA i1021Fi22RegB (i1021Fi22Word j)

@[expose] def i1021Fi22Check : Bool :=
  elem2OK (ops3 77) (List.ofFn i1021Fi22X) (List.range 77)

end CFSG.HardMathSupport.Solomon.Coordinator
