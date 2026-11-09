module

public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicScalar
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LargeEvenClassification.Helpers

@[expose] def c8FourPairing (v q : Fin 32) : ZMod 2 :=
  ((List.range 5).map (fun i => if v.val.testBit i && q.val.testBit i then (1 : ZMod 2) else 0)).sum

@[expose] def c8FourEncodeBits (f : Fin 5 → ZMod 2) : Fin 32 :=
  Fin.ofNat 32 (((List.finRange 5).map (fun i => if f i = 1 then 2 ^ i.val else 0)).sum)

theorem c8FourPairing_bit_xor : ∀ a b c : Bool,
    (if (a ^^ b) && c then (1 : ZMod 2) else 0) =
      (if a && c then 1 else 0) + (if b && c then 1 else 0) := by
  decide

theorem c8FourPairing_xor (v w q : Fin 32) :
    c8FourPairing (Fin.ofNat 32 (v.val ^^^ w.val)) q =
      c8FourPairing v q + c8FourPairing w q := by
  have hlt : v.val ^^^ w.val < 2 ^ 5 := Nat.xor_lt_two_pow v.isLt w.isLt
  have hval : (Fin.ofNat 32 (v.val ^^^ w.val)).val = v.val ^^^ w.val := by
    rw [Fin.val_ofNat]
    exact Nat.mod_eq_of_lt hlt
  unfold c8FourPairing
  rw [hval, ← List.sum_map_add]
  congr 1
  apply List.map_congr_left
  intro i _
  rw [Nat.testBit_xor]
  exact c8FourPairing_bit_xor _ _ _

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
