module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1TightGen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22TA
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22TData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22CheckInputs

public section

namespace CFSG.QuasithinUnique.Setup.X1
open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint

@[expose] def a2gens : List ↥m22A := [aA, bA, dA]

@[expose] def a2rg : List ↥m22A := a2RGens.map (evalN m22A a2gens)

@[expose] def a2rl : List ↥m22A := a2RWords.map (evalN m22A a2rg)

@[expose] def bE (i : Fin 5) : ↥m22A := (a2Bw.map (evalN m22A a2gens)).getD i.val 1

@[expose] def tE : ↥m22A := bE 0 * bE 1 * bE 2 * bE 3 * bE 4

@[expose] def cE : ↥m22A := evalN m22A a2gens a2Cw

@[expose] def dE : ↥m22A := evalN m22A a2gens a2Dw

@[expose] def a2e5 : List ↥m22A :=
  (List.range 32).map fun n =>
    (List.range 5).foldl (fun acc k => if n.testBit k then acc * (bE ⟨k % 5, by omega⟩) else acc) 1

@[expose] def a2heavy : List ↥m22A := heavyList a2rl a2e5 30

@[expose] def yT : ↥m22A := evalN m22A a2gens a2Wt

@[expose] def y0 : ↥m22A := evalN m22A a2gens a2W0

@[expose] def x2M : ↥NativeSporadic.M22 := evalN NativeSporadic.M22 [m22a, m22b] a2X2w

@[expose] def x4M : ↥NativeSporadic.M22 := evalN NativeSporadic.M22 [m22a, m22b] a2X4w

@[expose] def fgOK (FG : List (ℕ × ℕ × List ℤ × List ℤ × List ℤ)) : Bool :=
  FG.all fun f =>
    evalG [m22rl.getD f.1 1, m22rl.getD f.2.1 1,
        evalN NativeSporadic.M22 [m22a, m22b] f.2.2.1 * m22rl.getD f.1 1 *
          (evalN NativeSporadic.M22 [m22a, m22b] f.2.2.1)⁻¹,
        evalN NativeSporadic.M22 [m22a, m22b] f.2.2.1 * m22rl.getD f.2.1 1 *
          (evalN NativeSporadic.M22 [m22a, m22b] f.2.2.1)⁻¹] f.2.2.2.1 == m22a &&
      evalG [m22rl.getD f.1 1, m22rl.getD f.2.1 1,
        evalN NativeSporadic.M22 [m22a, m22b] f.2.2.1 * m22rl.getD f.1 1 *
          (evalN NativeSporadic.M22 [m22a, m22b] f.2.2.1)⁻¹,
        evalN NativeSporadic.M22 [m22a, m22b] f.2.2.1 * m22rl.getD f.2.1 1 *
          (evalN NativeSporadic.M22 [m22a, m22b] f.2.2.1)⁻¹] f.2.2.2.2 == m22b

end CFSG.QuasithinUnique.Setup.X1
