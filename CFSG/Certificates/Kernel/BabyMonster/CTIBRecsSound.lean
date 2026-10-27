module

public import CFSG.Certificates.Kernel.BabyMonster.CTIBNatsSound
public import Certificates.Data.CFSGNative.CTIB.Coset

public section

namespace CFSG.Monster.B.CTIB.Native

@[expose] noncomputable def recPieces (L : List Char) : List (List Char) :=
  List.splitOnPPrepend (· == ' ') L []

@[expose] noncomputable def recsOfChars (L : List Char) : List (Nat × Nat) :=
  orbitRecs.pairs ((recPieces L).filterMap pieceVal)

@[expose] noncomputable def recDigitsOK (L : List Char) : Bool :=
  (recPieces L).all fun p => p.all Char.isDigit

@[expose] noncomputable def recsLenOK (L : List Char) (n : Nat) : Bool :=
  recDigitsOK L && (recsOfChars L).length == n

@[expose] noncomputable def recsMemOK (L : List Char) (qs : List (Nat × Nat)) : Bool :=
  recDigitsOK L && qs.all fun q => (recsOfChars L).any fun r => r.1 == q.1 && r.2 == q.2

theorem pairs_parse {L : List Char} (h : recDigitsOK L = true) :
    orbitRecs.pairs (parseNats (String.ofList L)) = recsOfChars L := by
  unfold recDigitsOK at h
  rw [parseNats_ofList L fun p hp c hc => List.all_eq_true.1 (List.all_eq_true.1 h p hp) c hc]
  rfl

theorem pairs_len_of {L : List Char} {n : Nat} (h : recsLenOK L n = true) :
    (orbitRecs.pairs (parseNats (String.ofList L))).length = n := by
  unfold recsLenOK at h
  rw [Bool.and_eq_true, beq_iff_eq] at h
  rw [pairs_parse h.1, h.2]

theorem pairs_mem_of {L : List Char} {qs : List (Nat × Nat)} (h : recsMemOK L qs = true) :
    ∀ q ∈ qs, q ∈ orbitRecs.pairs (parseNats (String.ofList L)) := by
  unfold recsMemOK at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  intro q hq
  rw [pairs_parse h.1]
  obtain ⟨r, hr, e⟩ := List.any_eq_true.1 (h.2 q hq)
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at e
  rwa [← Prod.ext e.1 e.2]

end CFSG.Monster.B.CTIB.Native

end
