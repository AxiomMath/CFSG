
module

public import CFSG.Certificates.Kernel.Th.Max3S.DefsBase

public import CFSG.Sporadic.Th.Max3.InvolutionsInputs

public section

namespace CFSG.KC.Th.Max3S

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3

variable (A B : Array V4)

@[expose] def z : Array V4 := powRows (wordRows (x A B) (y A B) zWord) zExp

@[expose] def qs : Array (Array V4) :=
  Array.ofFn fun i : Fin 8 => powRows (wordRows (x A B) (y A B) (qWord i)) (qExp i)

@[expose] def q (i : Fin 8) : Array V4 := (qs A B)[i.val]'(by simp [qs])

@[expose] def nf (s : ℕ) (e : Fin 8 → ℕ) : Array V4 :=
  CFSG.Sporadic.Th.Native.mulRows (powRows (z A B) s) (prodRows (List.ofFn fun i => powRows (q A B i) (e i)))

@[expose] def nfTab : Array (Array V4) :=
  Array.ofFn fun k : Fin 512 => nf A B (k.val % 2) fun i => k.val / 2 ^ (i.val + 1) % 2

@[expose] def nfAt (k : Fin 512) : Array V4 := (nfTab A B)[k.val]'(by simp [nfTab])

@[expose] def d : Array V4 := wordRows (x A B) (y A B) InvRep.dWord

@[expose] def xNf (k : Fin 512) : Array V4 := CFSG.Sporadic.Th.Native.mulRows (x A B) (nfAt A B k)

@[expose] def dNf (k : Fin 512) : Array V4 := CFSG.Sporadic.Th.Native.mulRows (d A B) (nfAt A B k)

@[expose] def C10092 : Prop :=
  (eqRows (powRows (t8 A B) 3) idRows = true ∧
      eqRows (powRows (s8' A B) 19) idRows = true ∧
      eqRows (CFSG.Sporadic.Th.Native.mulRows (x A B) (x A B)) idRows = true ∧
      eqRows (powRows (y A B) 6) idRows = true ∧
      eqRows (z A B) A = true ∧
      eqRows (z A B) idRows = false ∧
      eqRows (CFSG.Sporadic.Th.Native.mulRows (z A B) (z A B)) idRows = true ∧
      eqRows (CFSG.Sporadic.Th.Native.mulRows (z A B) (x A B)) (CFSG.Sporadic.Th.Native.mulRows (x A B) (z A B)) = true ∧
      eqRows (CFSG.Sporadic.Th.Native.mulRows (z A B) (y A B)) (CFSG.Sporadic.Th.Native.mulRows (y A B) (z A B)) = true ∧
      (∀ i : Fin 8, eqRows (CFSG.Sporadic.Th.Native.mulRows (q A B i) (q A B i)) idRows = true) ∧
      (∀ i : Fin 8, eqRows (CFSG.Sporadic.Th.Native.mulRows (z A B) (q A B i)) (CFSG.Sporadic.Th.Native.mulRows (q A B i) (z A B)) = true) ∧
      (∀ i j : Fin 8, eqRows (CFSG.Sporadic.Th.Native.mulRows (q A B i) (q A B j))
        (CFSG.Sporadic.Th.Native.mulRows (CFSG.Sporadic.Th.Native.mulRows (q A B j) (q A B i)) (powRows (z A B) (c i j).val)) = true) ∧
      (∀ i : Fin 8, eqRows (CFSG.Sporadic.Th.Native.mulRows (CFSG.Sporadic.Th.Native.mulRows (x A B) (q A B i)) (x A B))
        (nf A B (xz i).val fun j => (xv i j).val) = true) ∧
      (∀ i : Fin 8, eqRows (CFSG.Sporadic.Th.Native.mulRows (CFSG.Sporadic.Th.Native.mulRows (y A B) (q A B i)) (powRows (y A B) 5))
        (nf A B (yz i).val fun j => (yv i j).val) = true))
    ∧ (∀ k l : Fin 512, l < k → eqRows (nfAt A B k) (nfAt A B l) = false)

@[expose] def C10089 : Prop :=
  (∀ k : Fin 512, eqRows (CFSG.Sporadic.Th.Native.mulRows (nfAt A B k) (nfAt A B k)) idRows = false ∨
      eqRows (nfAt A B k) idRows = true ∨ eqRows (nfAt A B k) (z A B) = true ∨
      eqRows (CFSG.Sporadic.Th.Native.mulRows (conj A B k) (q A B 0)) (CFSG.Sporadic.Th.Native.mulRows (nfAt A B k) (conj A B k)) = true) ∧
    (∀ k : Fin 512, eqRows (CFSG.Sporadic.Th.Native.mulRows (xNf A B k) (xNf A B k)) idRows = false ∨
      eqRows (CFSG.Sporadic.Th.Native.mulRows (nfAt A B (InvRep.uIdx k)) (x A B))
        (CFSG.Sporadic.Th.Native.mulRows (xNf A B k) (nfAt A B (InvRep.uIdx k))) = true) ∧
    (∀ k : Fin 512, eqRows (CFSG.Sporadic.Th.Native.mulRows (dNf A B k) (dNf A B k)) idRows = false)

end CFSG.KC.Th.Max3S

end
