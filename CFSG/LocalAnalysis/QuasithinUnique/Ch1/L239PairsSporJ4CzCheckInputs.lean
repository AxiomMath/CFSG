module

public import CFSG.Sporadic.J4.QT2ANative

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs
open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT2A

@[expose] def hePairs : List (Nat × Nat) := [(0, 1), (0, 2), (0, 3)]

@[expose] def hCommRows (k n : Nat) : Array V2 :=
  mulRows (mulRows (mulRows (qR k) (yEl n)) (wR (invW (qGenW.getD k []))))
    (mulRows (yEl n) (yEl n))

@[expose] def chkHE : Bool :=
  qGenW.all (fun w => w.all fun l => l != 0) &&
    (List.range 27).all fun n => n == 0 ||
      (eqRows (mulRows (yEl n) (mulRows (yEl n) (yEl n))) idRows &&
        hePairs.any fun p => wfR (hCommRows p.1 n) && wfR (hCommRows p.2 n) &&
          nocomm (hCommRows p.1 n) (hCommRows p.2 n))

end CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs
