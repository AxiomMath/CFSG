module

public import Certificates.Data.Kernel.Co1Fus
public import CFSG.Certificates.Kernel.LocalCompF2DagSound
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step18Co1Tests

public section

namespace CFSG.KC.F2Dag

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.Sporadic.Co1Schreier.Native
open CFSG.ComponentClassification.AS81.Co1Fusion

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem andB_eq_true {a b : Bool} : CFSG.KLie.CT.andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [CFSG.KLie.CT.andB]

theorem notB_eq_true {a : Bool} : CFSG.KLie.CT.notB a = true ↔ a = false := by
  cases a <;> simp [CFSG.KLie.CT.notB]

set_option exponentiation.threshold 600

theorem canon_lt {X : Nat} (h : canonF 24 X = true) : X < 2 ^ 576 := by
  have e : pw2 (Nat.mul 24 24) = 2 ^ 576 := by
    unfold pw2
    change 1 <<< (24 * 24) = 2 ^ 576
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  have h' : X < pw2 (Nat.mul 24 24) := by
    unfold canonF at h
    simpa using h
  rwa [e] at h'

theorem fusCheckOf_of_K {A B T : Nat} {tR : Rows} {ws : List (List Int)} {E EI : List Nat}
    {ix ic p k : Nat} (hA : aR = unpackF 24 A) (hB : bR = unpackF 24 B)
    (hT : tR = unpackF 24 T) (hb : E.take 3 = [A, B, T]) (hd : dagK 24 3 ws E EI = true)
    (hk : fusK 24 T E ix ic p k = true) : fusCheckOf tR ws ix ic p k = true := by
  have hD : dag [aR, bR, tR] ws = (E.map (unpackF 24), EI.map (unpackF 24), true) := by
    have h := dagK_sound hd
    rw [hb] at h
    rw [hA, hB, hT]
    simpa only [List.map_cons, List.map_nil] using h
  simp only [fusK, strictB_eq] at hk
  unfold fusAt at hk
  simp only [andB_eq_true, notB_eq_true] at hk
  obtain ⟨⟨k1, k2⟩, ⟨k3, k4⟩, ⟨k5, k6, k7⟩, ⟨k8, k9, k10⟩, e1, e2, e3, e4, e5, e6, e7⟩ := hk
  simp only [fusCheckOf, hD]
  rw [one_unpack, List.getD_map, List.getD_map, hT]
  simp only [pow_unpack, mul_unpack]
  rw [beq_unpack (canon_lt k1) (canon_lt k2), beq_unpack (canon_lt k3) (canon_lt k4),
    beq_unpack (canon_lt k5) (canon_lt k7), validRows_unpack, bne,
    beq_unpack (canon_lt k6) (canon_lt k7), beq_unpack (canon_lt k8) (canon_lt k7),
    beq_unpack (canon_lt k9) (canon_lt k7), validRows_unpack, bne,
    beq_unpack (canon_lt k10) (canon_lt k7), e1, e2, e3, e4, e5, e6, e7]
  rfl

end CFSG.KC.F2Dag

end
