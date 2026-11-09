module

public import CFSG.Certificates.Kernel.Co1FixCount
import Mathlib.Tactic.Ring

public section

namespace CFSG.KC.Co1QGram

open CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.Co1Fix CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.InvNative Matrix

@[expose] noncomputable def qf (Qt x : Nat) : Bool := dotK 24 x (vecK 24 Qt x)

@[expose] noncomputable def bf (Qt x y : Nat) : Bool :=
  Bool.xor (dotK 24 x (vecK 24 Qt y)) (dotK 24 y (vecK 24 Qt x))

@[expose] noncomputable def gcK (F : List Nat) : List Nat → List Bool → Bool → Nat → Nat :=
  List.rec (motive := fun _ => List Nat → List Bool → Bool → Nat → Nat)
    (fun _ _ v _ => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) v)
    (fun _ _ ih R Q v l =>
      List.casesOn (motive := fun _ => Nat) R (nat_lit 0) fun r R =>
      List.casesOn (motive := fun _ => Nat) Q (nat_lit 0) fun b Q =>
        strictN (Nat.shiftRight l (nat_lit 1)) fun l0 =>
        strictN (Nat.shiftRight (Nat.xor l r) (nat_lit 1)) fun l1 =>
        strictN (ih R Q v l0) fun x =>
        strictN (ih R Q (Bool.xor v (Bool.xor b (bit l (nat_lit 0)))) l1) fun y => Nat.add x y) F

@[expose] noncomputable def rowOK (Qt f : Nat) : List Nat → Nat → Bool
  | [], _ => true
  | g :: L, r => (r.testBit 0 == bf Qt f g) && rowOK Qt f L (r >>> 1)

@[expose] noncomputable def rowsOK (Qt : Nat) : List Nat → List Nat → List Bool → Bool
  | [], _, _ => true
  | f :: F, r :: R, b :: Q => (b == qf Qt f) && rowOK Qt f (f :: F) r && rowsOK Qt F R Q
  | _ :: _, _, _ => false

@[expose] noncomputable def zb (b : Bool) : ZMod 2 := if b = true then 1 else 0

theorem zb_xor (a b : Bool) : zb (Bool.xor a b) = zb a + zb b := by
  cases a <;> cases b <;> decide

theorem zb_inj {a b : Bool} (h : zb a = zb b) : a = b := by
  revert h
  cases a <;> cases b <;> decide

theorem zb_dot (Qt x y : Nat) :
    zb (dotK 24 x (vecK 24 Qt y)) = vecOf x ⬝ᵥ (vecOf y ᵥ* rowsMatrix 24 (unpackR 24 Qt)) := by
  show zb (dotK 24 x (vmF 24 Qt y)) = _
  rw [vecMul_eq, vecOf, vecOf, CFSG.Sporadic.Co1.Module.toVecD_dotProduct, zb, dotK_dotN]

theorem vecOf_xor (x y : Nat) : vecOf (x ^^^ y) = vecOf x + vecOf y := by
  rw [vecOf, vecOf, vecOf, toVecD_xor]

theorem qf_xor (Qt a f : Nat) :
    qf Qt (a ^^^ f) = Bool.xor (qf Qt a) (Bool.xor (qf Qt f) (bf Qt a f)) := by
  apply zb_inj
  simp only [qf, bf, zb_xor, zb_dot, vecOf_xor, add_vecMul, dotProduct_add, add_dotProduct]
  ring

theorem bf_xor (Qt a f g : Nat) : bf Qt (a ^^^ f) g = Bool.xor (bf Qt a g) (bf Qt f g) := by
  apply zb_inj
  simp only [bf, zb_xor, zb_dot, vecOf_xor, add_vecMul, dotProduct_add, add_dotProduct]
  ring

theorem gcK_cons (f : Nat) (F : List Nat) (r : Nat) (R : List Nat) (b : Bool) (Q : List Bool)
    (v : Bool) (l : Nat) :
    gcK (f :: F) (r :: R) (b :: Q) v l =
      gcK F R Q v (l >>> 1) +
        gcK F R Q (Bool.xor v (Bool.xor b (l.testBit 0))) ((l ^^^ r) >>> 1) := by
  have e : gcK (f :: F) (r :: R) (b :: Q) v l =
      strictN (Nat.shiftRight l 1) fun l0 => strictN (Nat.shiftRight (Nat.xor l r) 1) fun l1 =>
        strictN (gcK F R Q v l0) fun x =>
        strictN (gcK F R Q (Bool.xor v (Bool.xor b (bit l 0))) l1) fun y => Nat.add x y := rfl
  simp only [e, strictN_eq', bit_eq'] <;> rfl

theorem rowOK_spec (Qt f : Nat) : ∀ (L : List Nat) (r : Nat), rowOK Qt f L r = true →
    ∀ k (hk : k < L.length), r.testBit k = bf Qt f L[k]
  | [], _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | g :: L, r, h, k, hk => by
    simp only [rowOK, Bool.and_eq_true, beq_iff_eq] at h
    cases k with
    | zero => exact h.1
    | succ k =>
      have := rowOK_spec Qt f L _ h.2 k (by simpa using hk)
      rw [Nat.testBit_shiftRight] at this
      rw [List.getElem_cons_succ, ← this, Nat.add_comm]

theorem gcK_eq (Qt : Nat) : ∀ (F R : List Nat) (Q : List Bool), rowsOK Qt F R Q = true →
    ∀ (acc l : Nat), (∀ k (hk : k < F.length), l.testBit k = bf Qt acc F[k]) →
      gcK F R Q (qf Qt acc) l = qCountK 24 Qt F acc
  | [], _, _, _, _, _, _ => rfl
  | f :: F, r :: R, b :: Q, h, acc, l, hl => by
    simp only [rowsOK, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hb, hr⟩, hR⟩ := h
    have hr' := rowOK_spec Qt f _ r hr
    have h0 : l.testBit 0 = bf Qt acc f := hl 0 (by simp)
    rw [gcK_cons, qCountK_cons]
    congr 1
    · refine gcK_eq Qt F R Q hR acc _ fun k hk => ?_
      have h1 := hl (k + 1) (by simpa using hk)
      rw [List.getElem_cons_succ] at h1
      rw [Nat.testBit_shiftRight, Nat.add_comm, h1]
    · have hv : Bool.xor (qf Qt acc) (Bool.xor b (l.testBit 0)) = qf Qt (acc ^^^ f) := by
        rw [hb, h0, qf_xor]
      rw [hv]
      refine gcK_eq Qt F R Q hR (acc ^^^ f) _ fun k hk => ?_
      have h1 := hl (k + 1) (by simpa using hk)
      have h2 := hr' (k + 1) (by simpa using hk)
      rw [List.getElem_cons_succ] at h1 h2
      rw [Nat.testBit_shiftRight, Nat.testBit_xor, bf_xor, Nat.add_comm, h1, h2]
  | _ :: _, [], _, h, _, _, _ => by simp [rowsOK] at h
  | _ :: _, _ :: _, [], h, _, _, _ => by simp [rowsOK] at h

theorem qCount_of_gram {Qt acc l c : Nat} {F R : List Nat} {Q : List Bool}
    (hR : rowsOK Qt F R Q = true) (hl : rowOK Qt acc F l = true)
    (h : Nat.beq (gcK F R Q (qf Qt acc) l) c = true) : Nat.beq (qCountK 24 Qt F acc) c = true := by
  rw [← gcK_eq Qt F R Q hR acc l (rowOK_spec Qt acc F l hl)]
  exact h

theorem all_of_zip {p : Nat → Bool} {P : Nat → Nat → Bool}
    (hP : ∀ o e, P o e = true → p o = true) :
    ∀ (L E : List Nat), L.length = E.length → ((L.zip E).all fun x => P x.1 x.2) = true →
      L.all p = true
  | [], _, _, _ => rfl
  | _ :: _, [], hl, _ => absurd hl (by simp)
  | o :: L, e :: E, hl, h => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h ⊢
    exact ⟨hP o e h.1, all_of_zip hP L E (by simpa using hl) h.2⟩

@[expose] noncomputable def fixKq (d Mt : Nat) (F Y : List Nat) (k a : Nat) (q : Bool) : Bool :=
  andB (Nat.beq (lenL F) k) (andB (Nat.beq (Nat.add (lenL Y) k) d)
  (andB (Nat.beq a (pw2 k))
  (andB (List.rec (motive := fun _ => Bool) true
      (fun f _ ih => andB (Nat.blt f (pw2 d)) (andB (Nat.beq (vecK d Mt f) f) ih)) F)
  (andB (pivK d F (nat_lit 0))
  (andB (List.rec (motive := fun _ => Bool) true
      (fun y _ ih => andB (Nat.blt y (pw2 d)) ih) Y)
  (andB (pivK d (List.rec (motive := fun _ => List Nat) List.nil
      (fun y _ ih => List.cons (Nat.xor (vecK d Mt y) y) ih) Y) (nat_lit 0))
    q))))))

theorem fixK_eq_fixKq (d Mt Qt : Nat) (F Y : List Nat) (k a b : Nat) :
    fixK d Mt Qt F Y k a b = fixKq d Mt F Y k a (Nat.beq (qCountK d Qt F 0) b) := rfl

end CFSG.KC.Co1QGram

end
