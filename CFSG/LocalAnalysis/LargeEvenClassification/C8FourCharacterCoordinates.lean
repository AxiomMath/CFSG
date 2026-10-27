module

public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicScalar
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LargeEvenClassification.Helpers

@[expose] def c8FourPairing (v q : Fin 32) : ZMod 2 :=
  ((List.range 5).map (fun i => if v.val.testBit i && q.val.testBit i then (1 : ZMod 2) else 0)).sum

@[expose] def c8FourEncodeBits (f : Fin 5 → ZMod 2) : Fin 32 :=
  Fin.ofNat 32 (((List.finRange 5).map (fun i => if f i = 1 then 2 ^ i.val else 0)).sum)

set_option maxHeartbeats 8000000 in
theorem c8FourPairing_xor (v w q : Fin 32) :
    c8FourPairing (Fin.ofNat 32 (v.val ^^^ w.val)) q =
      c8FourPairing v q + c8FourPairing w q := by
  have h : ∀ v w q : Fin 32,
      c8FourPairing (Fin.ofNat 32 (v.val ^^^ w.val)) q =
        c8FourPairing v q + c8FourPairing w q := by decide +kernel
  exact h v w q

theorem c8FourPairing_zero (q : Fin 32) : c8FourPairing 0 q = 0 := by
  have h : ∀ q : Fin 32, c8FourPairing 0 q = 0 := by decide +kernel
  exact h q

set_option maxHeartbeats 8000000 in
theorem c8FourPairing_encode (f : Fin 5 → ZMod 2) (i : Fin 5) :
    c8FourPairing (Fin.ofNat 32 (2 ^ i.val)) (c8FourEncodeBits f) = f i := by
  have h : ∀ (f : Fin 5 → ZMod 2) (i : Fin 5),
      c8FourPairing (Fin.ofNat 32 (2 ^ i.val)) (c8FourEncodeBits f) = f i := by
    decide +kernel
  exact h f i

end CFSG.LargeEvenClassification.Helpers
