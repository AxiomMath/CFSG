module

public import CFSG.Sporadic.Co2Schreier.Arrays

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Co2Schreier

set_option compiler.extract_closed false

@[expose] def slpGo : Array (Array ℕ) → Array (Array ℕ) → List (List ℤ) → Array (Array ℕ)
  | A, _, [] => A
  | A, Ainv, w :: ds =>
    slpGo (A.push (wordA 2300 A Ainv w)) (Ainv.push (invCand 2300 (wordA 2300 A Ainv w))) ds

@[expose] def slpFinal (B : Array (Array ℕ)) (ds : List (List ℤ)) : Array (Array ℕ) :=
  slpGo B (rawInvs 2300 B) ds

@[expose] def slpOK (B : Array (Array ℕ)) (ds : List (List ℤ))
    (eqs nes : List (List ℤ × List ℤ)) : Bool :=
  extWordsOK B.size ds &&
    (let A := slpFinal B ds
     let Ainv := rawInvs 2300 A
     allInv A &&
       eqs.all (fun e => lettersOK A.size e.1 && lettersOK A.size e.2 &&
         eqA 2300 (wordA 2300 A Ainv e.1) (wordA 2300 A Ainv e.2)) &&
       nes.all (fun e => lettersOK A.size e.1 && lettersOK A.size e.2 &&
         !eqA 2300 (wordA 2300 A Ainv e.1) (wordA 2300 A Ainv e.2)))

@[expose] def slpTargets (B : Array (Array ℕ)) (ds : List (List ℤ))
    (tg : List (List ℤ × Array ℕ)) : Bool :=
  extWordsOK B.size ds &&
    (let A := slpFinal B ds
     let Ainv := rawInvs 2300 A
     allInv A &&
       tg.all (fun e => lettersOK A.size e.1 && eqA 2300 (wordA 2300 A Ainv e.1) e.2))

@[expose] def selArr (A : Array (Array ℕ)) (idx : List ℕ) : Array (Array ℕ) :=
  (idx.map fun i => A[i - 1]!).toArray

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2
