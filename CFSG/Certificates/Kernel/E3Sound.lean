module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Certificates.Kernel.Spor.CbfsFacts
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentTree
public import Certificates.Data.Kernel.Child3
public import Certificates.Data.Kernel.Fendel

public section

namespace CFSG.KC.E3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Fendel CFSG.KC.Child3
open CFSG.Monster.B.Co2.Native CFSG.EvenSmallLie.SympSix.Co3Ident

@[expose] def classDataG (L G : Array (Array ℕ)) (idx : Array ℕ → ℕ) (tst : Array ℕ → Bool) :
    Array ℕ × Array ℕ × Array ℕ := Id.run do
  let mut reps : Array ℕ := #[]
  let mut ck : Array ℕ := Array.replicate 4608 0
  let mut ci : Array ℕ := Array.replicate 4608 0
  let mut done : Array Bool := Array.replicate 4608 false
  for j in [0:4608] do
    if !done[j]! && tst L[j]! then
      let k := reps.size
      reps := reps.push j
      done := done.set! j true
      ck := ck.set! j k
      let mut queue : Array (ℕ × Array ℕ) := #[(j, idA 276)]
      let mut q := 0
      for _ in [0:4608] do
        if q < queue.size then
          let pc := queue[q]!
          q := q + 1
          for i in [0:3] do
            let g := G[i]!
            let p' := compA 276 g (compA 276 L[pc.1]! (invCand 276 g))
            let ip := idx p'
            if ip < 4608 && !done[ip]! then
              done := done.set! ip true
              let c' := compA 276 g pc.2
              ck := ck.set! ip k
              ci := ci.set! ip (idx (invCand 276 c'))
              queue := queue.push (ip, c')
  return (reps, ck, ci)

@[expose] def sigmaTabG (P L : Array ℕ) (Y : Array (Array ℕ)) : Array (Array ℕ) := Id.run do
  let mut T : Array (Array ℕ) := #[idA 276]
  for j in [1:4608] do
    T := T.push (compA 276 T[P[j]!]! Y[L[j]!]!)
  return T

end CFSG.KC.E3

end
