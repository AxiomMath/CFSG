module

public import Certificates.Data.Kernel.Co2U.Twin
public import CFSG.Certificates.Kernel.Co2Smith.RowsSound

public section

namespace CFSG.KC.Co2U

open CFSG.KC.Loop CFSG.KC.Co1F2 CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.KC.F2TriSep CFSG.KC.M1F2
  CFSG.GF2W1112 CFSG.Sporadic.SmallF2.Native

private theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem nthK_eq (P : List Nat) : ∀ i, nthK P i = P.getD i 0 := by
  induction P with
  | nil => intro i; rfl
  | cons p P ih =>
    intro i
    cases i with
    | zero => rfl
    | succ j => exact ih j

theorem w12UEqR_unpack (A B : Nat) : w12UEqR (unpackR 22 A) (unpackR 22 B) = eqK A B := by
  rw [← beq_unpack]
  apply Bool.eq_iff_iff.2
  rw [w12UEqR, List.all_eq_true, beq_iff_eq]
  constructor
  · intro h
    apply Array.ext
    · simp [unpackR]
    · intro i h1 _
      have hi : i < 22 := by simpa [unpackR] using h1
      have e := h i (List.mem_range.2 hi)
      simpa [unpackR, hi, Nat.mod_mod] using e
  · intro h i _
    rw [h]
    exact beq_self_eq_true _

theorem idxOk_cons (q : Nat × Nat) (L : List (Nat × Nat)) :
    w12UIdxOk (q :: L) = (decide (q.1 < 33) && w12UIdxOk L) := by
  rw [w12UIdxOk, w12UIdxOk, List.all_cons]

theorem foldl_unpack {G : Array (Array Nat)} {P : List Nat}
    (hG : ∀ i < 33, G[i]! = unpackR 22 (nthK P i)) :
    ∀ (L : List (Nat × Nat)), w12UIdxOk L = true → ∀ acc : Nat,
      L.foldl (fun acc q => mulRows 22 acc (powRows 22 G[q.1]! q.2)) (unpackR 22 acc) =
        unpackR 22 (evK P L acc)
  | [], _, acc => rfl
  | q :: L, h, acc => by
    rw [idxOk_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    have e : evK P (q :: L) acc = evK P L (mulV acc (powK (nthK P q.1) q.2)) := strictN_eq _ _
    rw [List.foldl_cons, hG q.1 h.1, powRows_unpack, mulRows_unpack, e]
    exact foldl_unpack hG L h.2 _

theorem evalE_unpack {G : Array (Array Nat)} {P : List Nat}
    (hG : ∀ i < 33, G[i]! = unpackR 22 (nthK P i)) {L : List (Nat × Nat)}
    (h : w12UIdxOk L = true) : w12UEvalE G L = unpackR 22 (evK P L IDP) := by
  rw [w12UEvalE, idRows_eq]
  exact foldl_unpack hG L h IDP

theorem eqCheck_eq {G : Array (Array Nat)} {P : List Nat}
    (hG : ∀ i < 33, G[i]! = unpackR 22 (nthK P i)) :
    ∀ eqs : List (List (Nat × Nat) × List (Nat × Nat)), w12UEqCheck G eqs = eqCheckK P eqs
  | [] => rfl
  | q :: eqs => by
    have e : eqCheckK P (q :: eqs) =
        ((w12UIdxOk q.1 && w12UIdxOk q.2 && eqK (evK P q.1 IDP) (evK P q.2 IDP)) &&
          eqCheckK P eqs) := rfl
    rw [e, ← eqCheck_eq hG eqs, w12UEqCheck, w12UEqCheck, List.all_cons]
    cases h1 : w12UIdxOk q.1
    · rfl
    cases h2 : w12UIdxOk q.2
    · rfl
    rw [evalE_unpack hG h1, evalE_unpack hG h2, w12UEqR_unpack]

theorem wordsK_map (A B : Nat) :
    ∀ (cs : List (List Char)) (P : List Nat), wordsK A B cs P = true →
      cs.map (fun c => unpackR 22 (wordB 22 A B (c.map (· == 'a')) (idF 22))) =
        P.map (unpackR 22)
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | c :: cs, p :: ps, h => by
    have e : wordsK A B (c :: cs) (p :: ps) =
        (eqK (wordB 22 A B (c.map (· == 'a')) (idF 22)) p && wordsK A B cs ps) := rfl
    rw [e, Bool.and_eq_true] at h
    rw [List.map_cons, List.map_cons, eq_unpack_of_eqK h.1, wordsK_map A B cs ps h.2]

end CFSG.KC.Co2U

end
