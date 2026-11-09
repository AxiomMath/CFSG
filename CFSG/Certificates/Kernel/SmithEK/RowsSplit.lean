module

public import Certificates.Data.Kernel.SmithEKP

public section

namespace CFSG.SmithE.K

theorem drop_succ_eq {α : Type} (l : List α) (n : Nat) : l.drop (n + 1) = l.tail.drop n := by
  cases l <;> simp

theorem drop_drop_add' {α : Type} (l : List α) (a n : Nat) :
    (l.drop a).drop n = l.drop (a + n) := by
  simp [List.drop_drop, Nat.add_comm]

theorem rowsF_nil (ONE REP DATA Bpk : Nat) (Qs Pl : List Nat) (Cr : List (List Nat)) (Pr : List Nat) :
    rowsF ONE REP DATA Bpk Qs Pl [] Cr Pr = true := rfl

theorem rowsF_cons (ONE REP DATA Bpk : Nat) (Qs Pl : List Nat) (p : Nat) (R : List Nat) (Cr : List (List Nat)) (Pr : List Nat) :
    rowsF ONE REP DATA Bpk Qs Pl (p :: R) Cr Pr =
      (rowF ONE REP DATA Bpk Qs Pl p (Cr.headD []) (Pr.headD 0) &&
        rowsF ONE REP DATA Bpk Qs Pl R Cr.tail Pr.tail) := rfl

theorem rowsF_append (ONE REP DATA Bpk : Nat) (Qs Pl : List Nat) : ∀ (R1 R2 : List Nat) (Cr : List (List Nat)) (Pr : List Nat),
    rowsF ONE REP DATA Bpk Qs Pl (R1 ++ R2) Cr Pr =
      (rowsF ONE REP DATA Bpk Qs Pl R1 Cr Pr &&
        rowsF ONE REP DATA Bpk Qs Pl R2 (Cr.drop R1.length) (Pr.drop R1.length))
  | [], R2, Cr, Pr => by
    rw [List.nil_append, rowsF_nil, Bool.true_and, List.length_nil, List.drop_zero, List.drop_zero]
  | p :: R1, R2, Cr, Pr => by
    rw [List.cons_append, rowsF_cons, rowsF_cons, rowsF_append ONE REP DATA Bpk Qs Pl R1 R2, Bool.and_assoc,
      List.length_cons, drop_succ_eq Cr, drop_succ_eq Pr]

theorem rowsF_chunks (ONE REP DATA Bpk : Nat) (Qs Pl : List Nat) (P : List Nat) (C : List (List Nat)) (Q : List Nat) (m : Nat) :
    ∀ (k lo : Nat), (P.drop lo).length ≤ k * m →
      (∀ j < k, rowsF ONE REP DATA Bpk Qs Pl ((P.drop (lo + j * m)).take m) (C.drop (lo + j * m))
        (Q.drop (lo + j * m)) = true) →
      rowsF ONE REP DATA Bpk Qs Pl (P.drop lo) (C.drop lo) (Q.drop lo) = true
  | 0, lo, hl, _ => by
    have e : P.drop lo = [] := List.eq_nil_of_length_eq_zero (by rw [Nat.zero_mul] at hl; omega)
    rw [e, rowsF_nil]
  | k + 1, lo, hl, h => by
    have h0 := h 0 (by omega)
    rw [Nat.zero_mul, Nat.add_zero] at h0
    rw [← List.take_append_drop m (P.drop lo), rowsF_append, h0, Bool.true_and]
    by_cases hm : m ≤ (P.drop lo).length
    · rw [List.length_take_of_le hm, drop_drop_add', drop_drop_add', drop_drop_add']
      refine rowsF_chunks ONE REP DATA Bpk Qs Pl P C Q m k (lo + m) ?_ fun j hj => ?_
      · rw [List.length_drop] at hl ⊢
        rw [Nat.add_mul, Nat.one_mul] at hl
        omega
      · have := h (j + 1) (by omega)
        rwa [show lo + (j + 1) * m = lo + m + j * m by rw [Nat.add_mul, Nat.one_mul]; omega] at this
    · have e : (P.drop lo).drop m = [] := List.drop_eq_nil_of_le (by omega)
      rw [e, rowsF_nil]

@[expose] def chkPFPre (P : List Nat) (C : List (List Nat)) : Bool :=
  P.length == 693 && C.length == 693 && P.all (fun p => decide (p < 4096)) &&
    C.all (fun c => c.length == 20 && c.all fun x => decide (x < 2 ^ 20))

@[expose] noncomputable def chkPFRows (P : List Nat) (C : List (List Nat)) (lo m : Nat) : Bool :=
  rowsF (pkW 400 (List.replicate 693 1) * l20) (pkW 400 (List.replicate 693 1))
    (pkW 400 (List.replicate 693 1) * (2 ^ 400 - 1)) (pkW 400 (C.map (pkW 20))) (qsOf C)
    (planesP P) ((P.drop lo).take m) (C.drop lo) ((C.map (pkW 20)).drop lo)

theorem chkPF_eq (P : List Nat) (C : List (List Nat)) :
    chkPF P C = (chkPFPre P C &&
      rowsF (pkW 400 (List.replicate 693 1) * l20) (pkW 400 (List.replicate 693 1))
        (pkW 400 (List.replicate 693 1) * (2 ^ 400 - 1)) (pkW 400 (C.map (pkW 20))) (qsOf C)
        (planesP P) P C (C.map (pkW 20))) := rfl

theorem chkPF_of (P : List Nat) (C : List (List Nat)) (m k : Nat) (hpre : chkPFPre P C = true)
    (hl : P.length ≤ k * m) (h : ∀ j < k, chkPFRows P C (0 + j * m) m = true) :
    chkPF P C = true := by
  rw [chkPF_eq, hpre, Bool.true_and]
  have := rowsF_chunks (pkW 400 (List.replicate 693 1) * l20) (pkW 400 (List.replicate 693 1))
    (pkW 400 (List.replicate 693 1) * (2 ^ 400 - 1)) (pkW 400 (C.map (pkW 20))) (qsOf C)
    (planesP P) P C (C.map (pkW 20)) m k 0 (by rw [List.drop_zero]; exact hl) h
  rw [List.drop_zero, List.drop_zero, List.drop_zero] at this
  exact this

end CFSG.SmithE.K

end
