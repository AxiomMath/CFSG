module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.FrameJSylInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUniqueData

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open CFSG.F3.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi22.Native
open CFSG.EvenSporadicStandard.TwoFi22.FrameJ (fjDLeaf)

set_option compiler.extract_closed false

@[expose] def uqPhiTab (B : Array Table) (m : Nat) : Table :=
  (List.range 10).foldr (fun i P => if m.testBit i then compT 3510 B[i]! P else P) (idT 3510)

@[expose] def uqD (t0 t1 : Array Table) (dp : Array (Nat × Nat)) : Array Table :=
  dp.map fun p => compT 3510 t0[p.1]! t1[p.2]!

@[expose] def uqBt (D : Array Table) (bas : Array Nat) : Array Table := bas.map fun j => D[j]!

@[expose] def uqActOK (t D B : Array Table) (sg : Array (Array Nat)) : Bool :=
  allIn 0 t.size fun k =>
    let Dt := D.map fun d => compT 3510 d t[k]!
    sg[k]!.size == 10 && allIn 0 10 fun i =>
      sg[k]![i]! < 22 && compT 3510 t[k]! B[i]! == Dt[sg[k]![i]!]!

@[expose] def uqTabCheckT (a : Table) (t0 t1 : Array Table) (dp : Array (Nat × Nat))
    (bas W : Array Nat) (sg0 sg1 : Array (Array Nat)) : Bool :=
  let D : Array Table := uqD t0 t1 dp
  let B : Array Table := uqBt D bas
  dp.size == 22 && bas.size == 10 && W.size == 22 && bas.all (· < 22) && W.all (· < 1024) &&
    dp.all (fun p => p.1 < t0.size && p.2 < t1.size && fjDLeaf a t0[p.1]! t1[p.2]!) &&
    allIn 0 22 (fun i => allIn 0 22 fun j => i == j || D[i]! != D[j]!) &&
    allIn 0 10 (fun i => allIn 0 10 fun j =>
      compT 3510 B[i]! B[j]! == compT 3510 B[j]! B[i]!) &&
    allIn 0 22 (fun j => uqPhiTab B W[j]! == D[j]!) &&
    sg0.size == t0.size && sg1.size == t1.size && uqActOK t0 D B sg0 && uqActOK t1 D B sg1

@[expose] def uqTabCheck (O : COrbit) (dp : Array (Nat × Nat)) (bas W : Array Nat)
    (sg0 sg1 : Array (Array Nat)) : Bool :=
  let L := sylLetters (chainLetters O)
  let T := chainTrees 3510 L sylBase
  uqTabCheckT O.alpha (treeTabs 3510 T[0]! L) (treeTabs 3510 T[1]! L) dp bas W sg0 sg1

@[expose] def uqTabCertificate : Bool := uqTabCheck (orbitData ()) uqDp uqBas uqW uqSg0 uqSg1

end CFSG.EvenSporadicStandard.TwoFi22.DS81
