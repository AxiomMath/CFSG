
module


public import CFSG.Certificates.Kernel.Th.Max3S.Defs
public import CFSG.Sporadic.Th.Max3.QuotientInputs
public import CFSG.Certificates.Kernel.Th.Spec.MirrorBase

public section

namespace CFSG.KC.Th.Max3S

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3
open CFSG.ComponentClassification.PresentationLocal (CarmichaelIndex)
open CFSG.Sporadic.Th.Max3.AltQuot (carmWord carmIdx carmCubeIdx carmPairIdx)

variable (A B : Array V4)

open CFSG.Sporadic.Th.Max3.AltQuot (carmWord carmIdx carmCubeIdx carmPairIdx)

@[expose] def abLetter (i : ℕ) : Array V4 := if i = 1 then A else B

@[expose] def ab (w : List ℕ) : Array V4 := prodRows (w.map (abLetter A B))

@[expose] def fusion (rg rgi rr : Array V4) : Array V4 :=
  Native.mulRows (powRows (Native.mulRows (Native.mulRows (Native.mulRows rgi rr) rg) A) 9) rgi

@[expose] def fusionX : Array V4 :=
  fusion A (ab A B fusionWordX) (ab A B (AllConj.invWord fusionWordX)) (x A B)

@[expose] def nfIdxRows (k : Fin 512) : Array V4 :=
  nf A B (k.val % 2) fun i => k.val / 2 ^ (i.val + 1) % 2

@[expose] def carm (k : CarmichaelIndex 9) : Array V4 := wordRows (x A B) (y A B) (carmWord k.1)

@[expose] def wa : Array V4 :=
  Native.mulRows (Native.mulRows (Native.mulRows (Native.mulRows (Native.mulRows
    (Native.mulRows (Native.mulRows (Native.mulRows
    (carm A B (carmIdx 2)) (powRows (carm A B (carmIdx 3)) 2)) (carm A B (carmIdx 2)))
    (carm A B (carmIdx 4))) (powRows (carm A B (carmIdx 5)) 2)) (carm A B (carmIdx 4)))
    (carm A B (carmIdx 6))) (powRows (carm A B (carmIdx 7)) 2)) (carm A B (carmIdx 6))

@[expose] def wb : Array V4 :=
  Native.mulRows (Native.mulRows (Native.mulRows (Native.mulRows (Native.mulRows
    (Native.mulRows (Native.mulRows
    (powRows (carm A B (carmIdx 2)) 2) (carm A B (carmIdx 3)))
    (powRows (carm A B (carmIdx 4)) 2)) (carm A B (carmIdx 3)))
    (powRows (carm A B (carmIdx 5)) 2)) (carm A B (carmIdx 6)))
    (powRows (carm A B (carmIdx 7)) 2)) (carm A B (carmIdx 8))

@[expose] def commXQ : Array V4 :=
  Native.mulRows (Native.mulRows (Native.mulRows (x A B) (q A B 1)) (x A B)) (q A B 1)

@[expose] def fusionQ0 : Array V4 :=
  fusion A (ab A B fusionWordQ0) (ab A B (AllConj.invWord fusionWordQ0)) (q A B 0)

@[expose] def eQ : Fin 4 → Array V4 :=
  ![q A B 0, Native.mulRows (q A B 1) (q A B 2), Native.mulRows (q A B 1) (q A B 5), q A B 7]

@[expose] def fQ : Fin 4 → Array V4 :=
  ![Native.mulRows (Native.mulRows (q A B 1) (q A B 3)) (q A B 4), q A B 3,
    Native.mulRows (q A B 3) (q A B 6), Native.mulRows (q A B 3) (q A B 4)]

@[expose] def C9014 : Prop :=
  (∀ i : Fin 4, eqRows (Native.mulRows (eQ A B i) (eQ A B i)) idRows = true) ∧
    (∀ i j : Fin 4,
      eqRows (Native.mulRows (eQ A B i) (eQ A B j)) (Native.mulRows (eQ A B j) (eQ A B i)) = true) ∧
    (∀ i : Fin 4, eqRows (Native.mulRows (fQ A B i) (eQ A B i))
      (Native.mulRows (Native.mulRows (eQ A B i) (z A B)) (fQ A B i)) = true) ∧
    (∀ i j : Fin 4, i ≠ j →
      eqRows (Native.mulRows (fQ A B j) (eQ A B i)) (Native.mulRows (eQ A B i) (fQ A B j)) = true)

@[expose] def C10088 : Prop :=
  eqRows (Native.mulRows (fusionQ0 A B) (q A B 0)) (Native.mulRows A (fusionQ0 A B)) = true ∧
    eqRows (Native.mulRows (fusionX A B) (x A B)) (Native.mulRows A (fusionX A B)) = true

@[expose] def C10090 : Prop :=
  eqRows (Spec.Mir.pW A B Packet.coreZWord) (z A B) = true ∧
    ∀ i : Fin 8, eqRows (Spec.Mir.pW A B (Packet.coreGeneratorWords i))
      (Native.mulRows (q A B i) (powRows (z A B) (qPShift i).val)) = true

@[expose] def C10091 : Prop :=
  (∀ k : CarmichaelIndex 9,
      eqRows (powRows (carm A B k) 3) (nfIdxRows A B (carmCubeIdx k)) = true) ∧
    (∀ j k : CarmichaelIndex 9, j.1 < k.1 →
      eqRows (powRows (Native.mulRows (carm A B j) (carm A B k)) 2)
        (nfIdxRows A B (carmPairIdx j k)) = true) ∧
    eqRows (Native.mulRows (x A B) (wa A B)) (nfIdxRows A B 299) = true ∧
    eqRows (Native.mulRows (powRows (y A B) 5) (wb A B)) (nfIdxRows A B 201) = true ∧
    eqRows (commXQ A B) idRows = false ∧ eqRows (commXQ A B) (z A B) = false

end CFSG.KC.Th.Max3S

end
