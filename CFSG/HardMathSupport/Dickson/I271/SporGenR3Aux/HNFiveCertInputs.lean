module

public import CFSG.Sporadic.HNSchreier.ThreeCheckInputs
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.HNFiveCertData
public meta import CFSG.Sporadic.HNSchreier.ThreeCheckInputs
public meta import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.HNFiveCertData

public section

namespace CFSG.HardMathSupport.Dickson.I271.HNFive.Native

open CFSG.ONSchreier.Native CFSG.Sporadic.HNSchreier.Native CFSG.Sporadic.F5.Native
open CFSG.Perm.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.He.Native

@[expose] def addM (p d : Nat) (X Y : Array (Array Nat)) : Array (Array Nat) :=
  Array.ofFn (n := d) fun i => Array.ofFn (n := d) fun j =>
    (X[i.val]![j.val]! + Y[i.val]![j.val]!) % p

@[expose] def subIdM (p d : Nat) (X : Array (Array Nat)) : Array (Array Nat) :=
  Array.ofFn (n := d) fun i => Array.ofFn (n := d) fun j =>
    (X[i.val]![j.val]! + (if i.val = j.val then p - 1 else 0)) % p

@[expose] def zeroM (d : Nat) : Array (Array Nat) := Array.replicate d (Array.replicate d 0)

@[expose] def neAt (p : Nat) (X Y : Array (Array Nat)) (i j : Nat) : Bool :=
  X[i]![j]! % p != Y[i]![j]! % p

@[expose] def tabMat (D : F5Data) (O : VOrbit) (Binv : Array (Array Nat)) (t : Array Nat) :
    Array (Array Nat) :=
  mulM 5 D.d (colsMat D.d (D.Q.map fun q => bytesToNats O.keys[t[q]!]!)) Binv

@[noinline, expose] def hn5Core (Ng Nc : Array (Array Nat)) : Bool :=
  let d := 133
  let I1 := idM d
  let Ny := powM 5 d Ng 6
  let Ns := powM 5 d Ng 10
  let Ngi := powM 5 d Ng 29
  let Nq := mulM 5 d (mulM 5 d (mulM 5 d (mulM 5 d Ngi Nc) Ng) Nc) Ngi
  let A := rowsOf 5 d dataA
  let Lam := rowsOf 5 d dataLam
  let R := rowsOf 5 d dataR
  let W := rowsOf 5 d dataW
  let Phi := rowsOf 5 d dataPhi
  let Ty := subIdM 5 d Ny
  let T2 := mulM 5 d Ty Ty
  let Z := zeroM d
  powM 5 d Ng 30 == I1 && neAt 5 Ny I1 0 1 && neAt 5 Ns I1 0 0 &&
    mulM 5 d Nq Ny == mulM 5 d Ny Nq &&
    neAt 5 (mulM 5 d Ns Nq) (mulM 5 d Nq Ns) 0 0 &&
    mulM 5 d Ty A == Z &&
    addM 5 d (mulM 5 d A Lam) (mulM 5 d R Ty) == I1 &&
    mulM 5 d (subIdM 5 d Nq) A == mulM 5 d T2 W &&
    mulM 5 d Phi T2 == Z &&
    neAt 5 (mulM 5 d (mulM 5 d Phi (subIdM 5 d Ns)) A) Z 0 1

@[noinline, expose] def hn5CheckO (O : VOrbit) : Bool :=
  let D := hnsData
  let n := D.n
  let a0 := natTab O.alpha
  let a1 := natTab O.beta
  let regs := progRegs n (initRegs n a0 a1) CFSG.Sporadic.HNSchreier.Data.subgroupProgram
  let hS := extendStrong n #[regs[1]!, regs[2]!] CFSG.Sporadic.HNSchreier.LocalData.strongWords
  let hSi := pinvs n hS
  let g3 := pcomp n (seedWordArr n a0 a1 CFSG.Sporadic.HNSchreier.FAData.g3Root)
    (pword n hS hSi CFSG.Sporadic.HNSchreier.FAData.g3H)
  let cT := seedWordArr n a0 a1 cWord
  let Binv := invM 5 D.d (colsMat D.d (D.Q.map fun q => bytesToNats O.keys[q]!))
  hn5Core (tabMat D O Binv g3) (tabMat D O Binv cT)

end CFSG.HardMathSupport.Dickson.I271.HNFive.Native
