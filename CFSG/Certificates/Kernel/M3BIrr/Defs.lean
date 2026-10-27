module

public import CFSG.HardMathSupport.MathTwE6.M3BIrrCheck

public section

namespace CFSG.KC.M3BIrr

open Timmesfeld.M3B CFSG.HardMathSupport.MathTwE6.M3BIrr

@[expose] def irrBody (A B : Mat) : Bool :=
  meq (mpow A 13) mone && meq (mpow B 11) mone &&
  meq (madd (madd (polyEval (idemCoeffs.getD 0 []) A) (polyEval (idemCoeffs.getD 1 []) A))
    (madd (polyEval (idemCoeffs.getD 2 []) A) (polyEval (idemCoeffs.getD 3 []) A))) mone &&
  idemOK A B 0 && idemOK A B 1 && idemOK A B 2 && idemOK A B 3

@[expose] def ofFlat (l : List Nat) : Mat := mofFn fun i j => Fin.ofNat 3 (l.getD (12 * i.val + j.val) 0)

@[expose] def pow2520 (G : Mat) : Mat := mpow (mpow (mpow (mpow G 8) 9) 5) 7

theorem irrCheck_eq : irrCheck () = irrBody (matA ()) (matB ()) := rfl

end CFSG.KC.M3BIrr

end
