module

public import Certificates.Data.Kernel.SporSch.LySyl
public import CFSG.Certificates.Kernel.SporSch.LyMatLemmas

public section

namespace CFSG.KS.SporSch.LySyl

open CFSG.KC.Enum CFSG.KC.Ord CFSG.KS CFSG.KS.SporSch.LyM CFSG.Sporadic.LySchreier.Native

@[expose] noncomputable def TBL (MT : Nat → Nat) (n : Nat) : Array (Array Nat) :=
  Array.ofFn (n := n) fun i => Array.ofFn (n := n) fun j => tmK MT i.val j.val

@[expose] noncomputable def recOf (w S : Nat) (E PL W : Nat → Nat) (c kg : Nat) :
    Array (Array (Array Nat)) × Array Nat × Array Nat × Array (Array Nat) :=
  (Array.ofFn (n := c) fun i => unpackL 111 w S (E i.val),
    Array.ofFn (n := c) fun i => parK PL i.val, Array.ofFn (n := c) fun i => labK PL i.val,
    Array.ofFn (n := kg) fun k => Array.ofFn (n := c) fun h => lamK W k.val h.val)

end CFSG.KS.SporSch.LySyl

end
