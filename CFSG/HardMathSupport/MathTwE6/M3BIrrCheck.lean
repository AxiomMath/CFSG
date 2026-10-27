module

public import Certificates.Data.CFSGNative.Timmesfeld.M3B

public section

set_option compiler.extract_closed false

namespace CFSG.HardMathSupport.MathTwE6.M3BIrr

open _root_.Timmesfeld.M3B (F3 Vec Mat WT fsum vget vofFn zeroV mget mofFn mmul mone meq mpow
  matOf LM mOfRows)

@[expose] def vmul (x : Vec) (A : Mat) : Vec := vofFn fun j => fsum 12 fun k => vget x k * mget A k j

@[expose] def axpy (c : F3) (x y : Vec) : Vec := vofFn fun i => vget x i + c * vget y i

@[expose] def vIsZero (x : Vec) : Bool := (List.finRange 12).all fun i => vget x i == 0

@[expose] def pivot (x : Vec) : Fin 12 := ((List.finRange 12).find? fun i => vget x i != 0).getD 0

@[expose] def reduce (bas : List (Fin 12 × Vec)) (x : Vec) : Vec :=
  bas.foldl (fun y pb => axpy (-(vget y pb.1)) y pb.2) x

@[expose] def elim (bas : List (Fin 12 × Vec)) (p : Fin 12) (r : Vec) : List (Fin 12 × Vec) :=
  bas.map fun qb => (qb.1, axpy (-(vget qb.2 p)) qb.2 r)

@[expose] def spinLoop (A B : Mat) : Nat → List (Fin 12 × Vec) → List Vec → List (Fin 12 × Vec)
  | 0, bas, _ => bas
  | _ + 1, bas, [] => bas
  | n + 1, bas, x :: q =>
    let r := reduce bas x
    if vIsZero r then spinLoop A B n bas q
    else
      let p := pivot r
      let r' := axpy (vget r p) zeroV r
      spinLoop A B n (elim bas p r' ++ [(p, r')]) (q ++ [vmul r' A, vmul r' B])

@[expose] def unitV (j : Fin 12) : Vec := vofFn fun i => if i = j then 1 else 0

@[expose] def veq (x y : Vec) : Bool := (List.finRange 12).all fun i => vget x i == vget y i

@[expose] def spinFull (A B : Mat) (v : Vec) : Bool :=
  let bas := spinLoop A B 64 [] [v]
  (List.finRange 12).all fun j => bas.any fun pb => veq pb.2 (unitV j)

@[expose] def madd (A B : Mat) : Mat := mofFn fun i j => mget A i j + mget B i j

@[expose] def mzero : Mat := mofFn fun _ _ => 0

@[expose] def polyEval (cs : List Nat) (A : Mat) : Mat :=
  cs.foldr (fun c P => madd (mofFn fun i j => if i = j then Fin.ofNat 3 c else 0) (mmul A P)) mzero

@[expose] def w₁ : WT := .mul (.mul (.mul (.gen 1) (.gen 0)) (.gen 3)) (.gen 2)

@[expose] def w₂ : WT := .mul (.mul (.pow (.gen 2) 3) (.gen 1)) (.gen 2)

@[expose] def matA (_ : Unit := ()) : Mat := mpow (matOf (LM ()) w₁) 2520

@[expose] def matB (_ : Unit := ()) : Mat := mpow (matOf (LM ()) w₂) 2520

@[expose] def idemCoeffs : List (List Nat) :=
  [[0, 2, 1, 2, 0, 1, 1, 2, 2, 2, 0, 2],
   [1, 1, 0, 1, 0, 0, 0, 2, 2, 1, 0, 2],
   [1, 2, 1, 2, 0, 1, 1, 0, 0, 2],
   [2, 1, 1, 1, 0, 1, 1, 2, 2, 1, 0, 2]]

@[expose] def bRows : List (List (List Nat)) :=
  [[[0, 1, 2, 1, 2, 0, 0, 1, 2, 0, 2, 2],
    [1, 0, 0, 1, 1, 2, 0, 2, 2, 2, 2, 1],
    [0, 0, 1, 1, 1, 2, 1, 0, 2, 2, 1, 0]],
   [[1, 1, 1, 2, 2, 1, 0, 1, 0, 2, 2, 1],
    [0, 0, 1, 0, 1, 2, 1, 0, 2, 1, 0, 0],
    [0, 1, 0, 1, 2, 1, 1, 2, 2, 1, 0, 0]],
   [[1, 0, 0, 1, 1, 2, 2, 2, 2, 0, 2, 0],
    [0, 1, 2, 1, 2, 1, 0, 0, 1, 2, 2, 1],
    [0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 2, 1]],
   [[1, 0, 2, 2, 1, 0, 2, 2, 0, 2, 2, 2],
    [0, 1, 2, 2, 2, 2, 2, 0, 1, 0, 0, 1],
    [0, 0, 1, 2, 0, 2, 0, 1, 0, 0, 1, 2]]]

@[expose] def cRows : List (List (List Nat)) :=
  [[[2, 0, 0],
    [2, 0, 0],
    [0, 1, 0],
    [0, 2, 1],
    [1, 0, 1],
    [2, 2, 0],
    [2, 2, 1],
    [1, 2, 2],
    [0, 0, 0],
    [2, 2, 1],
    [1, 2, 2],
    [0, 1, 0]],
   [[1, 0, 0],
    [2, 0, 0],
    [2, 2, 0],
    [0, 2, 2],
    [2, 2, 1],
    [0, 0, 2],
    [0, 2, 2],
    [2, 0, 0],
    [0, 0, 2],
    [2, 1, 1],
    [1, 2, 0],
    [2, 2, 2]],
   [[1, 0, 0],
    [1, 1, 0],
    [1, 2, 2],
    [0, 0, 0],
    [0, 2, 0],
    [2, 1, 0],
    [2, 2, 0],
    [1, 0, 1],
    [1, 2, 2],
    [0, 0, 0],
    [0, 0, 0],
    [0, 1, 0]],
   [[2, 0, 0],
    [0, 2, 0],
    [2, 2, 1],
    [1, 1, 2],
    [1, 0, 2],
    [2, 1, 0],
    [2, 0, 0],
    [1, 0, 0],
    [2, 2, 1],
    [2, 1, 1],
    [0, 1, 0],
    [0, 1, 1]]]

@[expose] def matBi (i : Nat) : Mat := mOfRows (bRows.getD i [])

@[expose] def matCi (i : Nat) : Mat := mOfRows (cRows.getD i [])

@[expose] def vec3 (a₀ a₁ a₂ : F3) : Vec :=
  vofFn fun j => if j.val = 0 then a₀ else if j.val = 1 then a₁ else if j.val = 2 then a₂ else 0

@[expose] def idemOK (A B : Mat) (i : Nat) : Bool :=
  let Ci := matCi i
  let Bi := matBi i
  meq (polyEval (idemCoeffs.getD i []) A) (mmul Ci Bi) &&
  (List.finRange 12).all (fun r => (List.finRange 12).all fun c => decide (c.val < 3) || mget Ci r c == 0) &&
  (List.finRange 3).all fun a₀ => (List.finRange 3).all fun a₁ => (List.finRange 3).all fun a₂ =>
    (a₀ == 0 && a₁ == 0 && a₂ == 0) || spinFull A B (vmul (vec3 a₀ a₁ a₂) Bi)

@[expose] def irrCheck (_ : Unit := ()) : Bool :=
  let A := matA ()
  let B := matB ()
  meq (mpow A 13) mone && meq (mpow B 11) mone &&
  meq (madd (madd (polyEval (idemCoeffs.getD 0 []) A) (polyEval (idemCoeffs.getD 1 []) A))
    (madd (polyEval (idemCoeffs.getD 2 []) A) (polyEval (idemCoeffs.getD 3 []) A))) mone &&
  idemOK A B 0 && idemOK A B 1 && idemOK A B 2 && idemOK A B 3

end CFSG.HardMathSupport.MathTwE6.M3BIrr
