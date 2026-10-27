module

public import CFSG.Sporadic.ThSchreier.TwoCentralizerInputs

@[expose] public section

namespace CFSG.KC.Th.Spec.Mir

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.Sporadic.ThSchreier

@[expose] def lett3 (P Q : Array V4) (l : ℤ) : Array V4 :=
  if l = 1 ∨ l = -1 then P else if l = 2 then Q else Native.mulRows Q Q

@[expose] def lx (RA RB : Array V4) : Array V4 := signedRows (lett3 RA RB) (Native.xWord ())

@[expose] def ly (RA RB : Array V4) : Array V4 := signedRows (lett3 RA RB) (Native.yWord ())

@[expose] def hR (RA RB : Array V4) (w : List ℤ) : Array V4 :=
  signedRows (lett3 (lx RA RB) (ly RA RB)) w

@[expose] def tw4 (RA RB : Array V4) : List (Array V4) :=
  [hR RA RB centWord0, hR RA RB centWord1,
    Native.mulRows (Native.mulRows (hR RA RB kWord) (hR RA RB centWord0))
      (hR RA RB (invWord kWord)),
    Native.mulRows (Native.mulRows (hR RA RB kWord) (hR RA RB centWord1))
      (hR RA RB (invWord kWord))]

@[expose] def twL (RA RB : Array V4) : List (Array V4) := strongWords.foldl twoRowsStep (tw4 RA RB)

@[expose] def rv (RA RB : Array V4) : Array V4 := signedRows (lett3 RA RB) transporterWord

@[expose] def rvi (RA RB : Array V4) : Array V4 :=
  signedRows (lett3 RA RB) (invWord transporterWord)

@[expose] def rT (RA RB : Array V4) : Array V4 :=
  Native.mulRows (Native.mulRows (rvi RA RB) RA) (rv RA RB)

@[expose] def rG (RA RB : Array V4) : Array V4 :=
  Native.mulRows (Native.mulRows (rv RA RB) (hR RA RB kWord)) (rvi RA RB)

@[expose] def rGi (RA RB : Array V4) : Array V4 :=
  Native.mulRows (Native.mulRows (rv RA RB) (hR RA RB (invWord kWord))) (rvi RA RB)

@[expose] def rR (RA RB : Array V4) : Array V4 :=
  Native.mulRows (Native.mulRows (rG RA RB) RA) (rGi RA RB)

@[expose] def m3t3 (RA RB : Array V4) : Array V4 := Native.mulRows RA RB

@[expose] def m3t4 (RA RB : Array V4) : Array V4 := Native.mulRows (m3t3 RA RB) RB

@[expose] def m3t5 (RA RB : Array V4) : Array V4 := Native.mulRows (m3t3 RA RB) (m3t4 RA RB)

@[expose] def m3t6 (RA RB : Array V4) : Array V4 := Native.mulRows (m3t3 RA RB) (m3t5 RA RB)

@[expose] def m3t7 (RA RB : Array V4) : Array V4 := Native.mulRows RA (m3t6 RA RB)

@[expose] def m3t8 (RA RB : Array V4) : Array V4 := Native.mulRows (m3t6 RA RB) RA

@[expose] def m3u (RA RB : Array V4) : Array V4 :=
  Native.mulRows (powRows (m3t8 RA RB) 2) (m3t7 RA RB)

@[expose] def m3s8 (RA RB : Array V4) : Array V4 := Native.mulRows (m3t6 RA RB) (m3t5 RA RB)

@[expose] def m3s9 (RA RB : Array V4) : Array V4 := Native.mulRows (m3t3 RA RB) (m3s8 RA RB)

@[expose] def m3s10 (RA RB : Array V4) : Array V4 := Native.mulRows (m3s9 RA RB) (m3t4 RA RB)

@[expose] def m3s7 (RA RB : Array V4) : Array V4 := Native.mulRows RA (m3s10 RA RB)

@[expose] def m3s8' (RA RB : Array V4) : Array V4 := Native.mulRows (m3s10 RA RB) RA

@[expose] def m3v (RA RB : Array V4) : Array V4 :=
  Native.mulRows (powRows (m3s8' RA RB) 18) (m3s7 RA RB)

@[expose] def m3x (RA RB : Array V4) : Array V4 := powRows (m3v RA RB) 14

@[expose] def m3y (RA RB : Array V4) : Array V4 :=
  Native.mulRows (m3t7 RA RB) (powRows (m3u RA RB) 9)

@[expose] def pLet (RA RB : Array V4) (l : ℤ) : Array V4 :=
  if l = 1 ∨ l = -1 then m3x RA RB else if l = 2 then m3y RA RB
  else if l = -2 then powRows (m3y RA RB) 5 else idRows

@[expose] def pW (RA RB : Array V4) (w : List ℤ) : Array V4 := prodRows (w.map (pLet RA RB))

@[expose] def rE217 (RA RB : Array V4) : Array V4 :=
  Native.mulRows (Native.mulRows (Native.mulRows (Native.mulRows (pW RA RB Packet.coreZWord)
    (pW RA RB (Packet.coreGeneratorWords 2))) (pW RA RB (Packet.coreGeneratorWords 3)))
    (pW RA RB (Packet.coreGeneratorWords 5))) (pW RA RB (Packet.coreGeneratorWords 6))

end CFSG.KC.Th.Spec.Mir

end
