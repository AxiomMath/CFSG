module

public import Certificates.Data.Kernel.Co1OddB
public import CFSG.Certificates.Kernel.Co1BWordSound
public import CFSG.Certificates.Kernel.Co1BSound
public import CFSG.Certificates.Kernel.Co1BInvSound
public import CFSG.Sporadic.Schreier.Co1OddBCheckInputs
import CFSG.Certificates.Kernel.SporSch.PairJ3FaithSound

public section

namespace CFSG.KC.Co1OddB

open CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KC.M1F2 CFSG.KC.F2W CFSG.KLie.CT
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.OddNative CFSG.Sporadic.Co1Schreier.Native
open CFSG.KS.SporSch.PF2 (mulF_row)

theorem idRows_eq : idRows 24 = unpackR 24 oneK := unpackR_idF.symm

theorem line_sound {A B V : Nat} {w : List (Nat × Nat)} (h : progK 24 [A, B, V] [w] 2 = true) :
    lineRows #[unpackR 24 A, unpackR 24 B] w = unpackR 24 V := by
  have e := prog_sound h
  have e2 : (([A, B, V].take 2).map (unpackR 24)).toArray = #[unpackR 24 A, unpackR 24 B] := rfl
  rw [e2] at e
  have e3 : runRows #[unpackR 24 A, unpackR 24 B] [w] =
      #[unpackR 24 A, unpackR 24 B, lineRows #[unpackR 24 A, unpackR 24 B] w] := rfl
  rw [e3] at e
  have e4 := congrArg (fun a : Array (Array Nat) => a[2]?) e
  simpa using e4

theorem lines_sound {A B : Nat} : ∀ (ws : List (List (Nat × Nat))) (Vs : List Nat),
    ((ws.zip Vs).all fun p => progK 24 [A, B, p.2] [p.1] 2) = true → ws.length = Vs.length →
    ws.map (lineRows #[unpackR 24 A, unpackR 24 B]) = Vs.map (unpackR 24)
  | [], [], _, _ => rfl
  | w :: ws, V :: Vs, h, hl => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h
    simp only [List.map_cons, line_sound h.1, lines_sound ws Vs h.2 (by simpa using hl)]
  | [], _ :: _, _, hl => absurd hl (by simp)
  | _ :: _, [], _, hl => absurd hl (by simp)

theorem us_eq {HP : List Nat} (hl : HP.length = 24) (u0 u1 : Nat) :
    oddUs (HP.map (unpackR 24)).toArray u0 u1 = unpackR 24 (usK HP u0 u1) := by
  unfold oddUs
  conv_rhs => rw [unpackR]
  congr 1
  funext i
  have hi : i.val < HP.length := by rw [hl]; exact i.isLt
  have hget : (HP.map (unpackR 24)).toArray[i.val]! = unpackR 24 (HP.getD i.val 0) := by
    rw [getElem!_pos _ i.val (by simpa using hi)]
    simp [List.getD_eq_getElem?_getD, hi]
  rw [hget, transposeRows_unpackR, vecMulN_unpackR, ← rowF_eq, usK,
    rowF_orN 24 (fun j _ => by split <;> exact vmF_lt 24 _ _) i.isLt]
  unfold rowU
  split <;> rfl

theorem get_unpackR (M : Nat) {i : Nat} (hi : i < 24) :
    (unpackR 24 M)[i]! = M / 2 ^ (24 * i) % 2 ^ 24 := by
  rw [getElem!_pos (unpackR 24 M) i (by simp [unpackR, hi])]
  simp [unpackR]

theorem ne_iff (A B : Nat) : (unpackR 24 A != unpackR 24 B) = !eqK A B := by
  rw [bne, beq_unpack]

theorem rows_eq (B M U : Nat) : ((List.range 24).all fun i =>
    vecMulN 24 (unpackR 24 M) (unpackR 24 B)[i]! == (unpackR 24 U)[i]!) = eqK (mulF 24 B M) U := by
  rw [← beq_unpack]
  apply Bool.eq_iff_iff.mpr
  rw [List.all_eq_true, beq_iff_eq]
  constructor
  · intro h
    rw [unpackR, unpackR]
    congr 1
    funext i
    have hi := h i.val (List.mem_range.mpr i.isLt)
    rw [beq_iff_eq, vecMulN_unpackR, get_unpackR _ i.isLt, get_unpackR _ i.isLt, ← rowF_eq,
      ← mulF_row 24 B M i.val i.isLt, rowF_eq] at hi
    exact hi
  · intro h i hi
    have hi' : i < 24 := List.mem_range.mp hi
    rw [beq_iff_eq, vecMulN_unpackR, get_unpackR _ hi', get_unpackR _ hi', ← rowF_eq,
      ← mulF_row 24 B M i hi', rowF_eq, ← get_unpackR _ hi', ← get_unpackR _ hi', h]

theorem cand_eq {HP : List Nat} (hl : HP.length = 24) (X Y S BT BTI u0 u1 : Nat) :
    oddCandOK (unpackR 24 X) (unpackR 24 Y) (unpackR 24 S) (HP.map (unpackR 24)).toArray
      (unpackR 24 BT) (unpackR 24 BTI) u0 u1 = candK X Y S HP BT BTI u0 u1 := by
  simp only [oddCandOK, candK]
  rw [us_eq hl, mulRows_unpackW, transposeRows_unpackR, transposeRows_unpackR, rows_eq,
    ← mulW_eq, mulRows_unpackW, mulRows_unpackW, mulRows_unpackW, mulRows_unpackW,
    mulRows_unpackW, mulRows_unpackW, beq_unpack, beq_unpack, beq_unpack, idRows_eq, ne_iff]
  have hp : ∀ p, (powRows 24 (unpackR 24 (trK 24 (mulW 24 BTI (usK HP u0 u1)))) p !=
      unpackR 24 oneK) = !eqK (powWK (trK 24 (mulW 24 BTI (usK HP u0 u1))) p) oneK := by
    intro p
    rw [powRows_eq _ idRows_eq, ne_iff]
  simp only [hp]

section Mat

open CFSG.Sporadic.SmallF2
open scoped Matrix

noncomputable def mat (A : Nat) : Matrix (Fin 24) (Fin 24) (ZMod 2) := rowsMatrix 24 (unpackR 24 A)

theorem unpackR_inj {A B : Nat} (h : mat A = mat B) : unpackR 24 A = unpackR 24 B := by
  unfold unpackR
  congr 1
  funext i
  apply toVecD_injective (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by positivity))
  funext j
  have e := congrArg (fun M => M i j) h
  simpa [mat, rowsMatrix_apply, unpackR] using e

theorem eqK_mat (A B : Nat) : eqK A B = decide (mat A = mat B) := by
  rw [← beq_unpack]
  by_cases h : mat A = mat B
  · rw [decide_eq_true h, unpackR_inj h]
    exact beq_self_eq_true _
  · rw [decide_eq_false h]
    exact beq_false_of_ne fun e => h (by rw [mat, mat, e])

theorem mat_mulW (A B : Nat) : mat (mulW 24 A B) = mat A * mat B := by
  rw [mat, ← mulRows_unpackW, rowsMatrix_mulRows]
  rfl

theorem mat_trK (A : Nat) : mat (trK 24 A) = (mat A)ᵀ := by
  rw [mat, ← transposeRows_unpackR, rowsMatrix_transposeRows]
  rfl

theorem mat_one : mat oneK = 1 := by
  rw [mat, ← idRows_eq, rowsMatrix_idRows]

theorem mat_pow (A p : Nat) : mat (powWK A p) = mat A ^ p := by
  rw [mat, ← powRows_eq A idRows_eq, rowsMatrix_powRows]
  rfl

theorem comm_tr (P Q : Matrix (Fin 24) (Fin 24) (ZMod 2)) :
    (Pᵀ * Q = Q * Pᵀ) = (Qᵀ * P = P * Qᵀ) := by
  apply propext
  constructor
  · intro h
    have e := congrArg Matrix.transpose h
    rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at e
  · intro h
    have e := congrArg Matrix.transpose h
    rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at e

theorem tr_eq_one (P : Matrix (Fin 24) (Fin 24) (ZMod 2)) : (Pᵀ = 1) = (P = 1) := by
  apply propext
  constructor
  · intro h
    have e := congrArg Matrix.transpose h
    rwa [Matrix.transpose_transpose, Matrix.transpose_one] at e
  · intro h
    rw [h, Matrix.transpose_one]

theorem candK_eq_candM (X Y S : Nat) (HP : List Nat) (BT BTI u0 u1 : Nat) :
    candK X Y S HP BT BTI u0 u1 =
      candM (trK 24 X) (trK 24 Y) (trK 24 S) BT BTI (usK HP u0 u1) := by
  simp only [candK, candM, eqK_mat, mat_mulW, mat_trK, mat_one, mat_pow,
    Matrix.transpose_transpose, ← Matrix.transpose_pow, tr_eq_one, comm_tr]

end Mat

end CFSG.KC.Co1OddB

end
