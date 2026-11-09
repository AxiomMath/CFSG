module

public import Certificates.Data.Kernel.Misc.HexDrop
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.Misc.HexFlat

open CFSG.KC.Enum CFSG.KS CFSG.KS.Text

@[expose] noncomputable def takeL (m : Nat) (cs : List Char) : List Char :=
  List.rec (motive := fun _ => Nat → List Char) (fun _ => List.nil)
    (fun c _ ih k => Nat.rec (motive := fun _ => List Char) List.nil
      (fun k' _ => List.cons c (ih k')) k) cs m

theorem takeL_dropL : ∀ (m : Nat) (cs : List Char), takeL m cs ++ dropL m cs = cs
  | 0, [] => rfl
  | 0, _ :: _ => rfl
  | _ + 1, [] => rfl
  | m + 1, c :: cs => by
    change c :: (takeL m cs ++ dropL m cs) = c :: cs
    rw [takeL_dropL m cs]

@[expose] noncomputable def body (d n w : Nat) (F : Nat → Nat) (ch : Char)
    (ih : Nat → Nat → Nat → Nat → Nat → Bool) (j e t v acc : Nat) : Bool :=
  strictB (hexV (Char.toNat ch)) (fun h => bIf(Nat.blt h (nat_lit 16),
    strictB (Nat.add (Nat.mul v (nat_lit 16)) h) (fun v' =>
    bIf(Nat.beq (Nat.succ t) d,
      bIf(Nat.blt v' (Nat.shiftLeft (nat_lit 1) w),
        strictB (Nat.lor acc (Nat.shiftLeft v' (Nat.mul w e))) (fun acc' =>
          bIf(Nat.beq (Nat.succ e) n,
            bAnd(Nat.beq acc' (F j),
              ih (Nat.succ j) (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0)),
            ih j (Nat.succ e) (nat_lit 0) (nat_lit 0) acc')),
        false),
      ih j e (Nat.succ t) v' acc)),
    false))

@[expose] noncomputable def runX (d n w N : Nat) (F : Nat → Nat) (cs : List Char) :
    Nat → Nat → Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Bool)
    (fun j _ _ _ _ => Nat.beq j N)
    (fun ch _ ih j e t v acc => bIf(Nat.beq j N, false, body d n w F ch ih j e t v acc)) cs

theorem glue_run_cons (d n w N : Nat) (F : Nat → Nat) (ch : Char) (L : List Char)
    (j e t v acc : Nat) :
    run d n w N F (ch :: L) j e t v acc =
      bIf(Nat.beq j N, true, body d n w F ch (run d n w N F L) j e t v acc) := rfl

theorem runX_cons (d n w N : Nat) (F : Nat → Nat) (ch : Char) (L : List Char)
    (j e t v acc : Nat) :
    runX d n w N F (ch :: L) j e t v acc =
      bIf(Nat.beq j N, false, body d n w F ch (runX d n w N F L) j e t v acc) := rfl

theorem sB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem beqF {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem body_spec (d n w : Nat) (F : Nat → Nat) (ch : Char) (j e t v acc : Nat) :
    (∀ ih, body d n w F ch ih j e t v acc = false) ∨
    (∃ e' t' v' a', ∀ ih, body d n w F ch ih j e t v acc = ih j e' t' v' a') ∨
    (∃ c, ∀ ih, body d n w F ch ih j e t v acc =
      bAnd(c, ih (Nat.succ j) (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0))) := by
  unfold body
  simp only [sB]
  cases Nat.blt (hexV (Char.toNat ch)) (nat_lit 16)
  · exact Or.inl fun _ => rfl
  · cases Nat.beq (Nat.succ t) d
    · exact Or.inr (Or.inl ⟨_, _, _, _, fun _ => rfl⟩)
    · cases Nat.blt (Nat.add (Nat.mul v (nat_lit 16)) (hexV (Char.toNat ch)))
        (Nat.shiftLeft (nat_lit 1) w)
      · exact Or.inl fun _ => rfl
      · cases Nat.beq (Nat.succ e) n
        · exact Or.inr (Or.inl ⟨_, _, _, _, fun _ => rfl⟩)
        · exact Or.inr (Or.inr ⟨_, fun _ => rfl⟩)

theorem run_append {d n w b N : Nat} {F : Nat → Nat} (hbN : b ≤ N) :
    ∀ (L1 L2 : List Char) (j e t v acc : Nat), j < b →
      runX d n w b F L1 j e t v acc = true →
      run d n w N F (L1 ++ L2) j e t v acc = run d n w N F L2 b 0 0 0 0
  | [], _, j, _, _, _, _, hj, h => by
    have h' : Nat.beq j b = true := h
    exact absurd (Nat.eq_of_beq_eq_true h') (by omega)
  | ch :: L1, L2, j, e, t, v, acc, hj, h => by
    have hjb : Nat.beq j b = false := beqF (by omega)
    have hjN : Nat.beq j N = false := beqF (by omega)
    rw [runX_cons, hjb] at h
    change body d n w F ch (runX d n w b F L1) j e t v acc = true at h
    rw [List.cons_append, glue_run_cons, hjN]
    change body d n w F ch (run d n w N F (L1 ++ L2)) j e t v acc = _
    rcases body_spec d n w F ch j e t v acc with hA | ⟨e', t', v', a', hB⟩ | ⟨c, hC⟩
    · rw [hA] at h
      exact absurd h Bool.false_ne_true
    · rw [hB] at h
      rw [hB]
      exact run_append hbN L1 L2 j e' t' v' a' hj h
    · rw [hC] at h
      rw [hC]
      cases c
      · change false = true at h
        exact absurd h Bool.false_ne_true
      · change runX d n w b F L1 (Nat.succ j) 0 0 0 0 = true at h
        change run d n w N F (L1 ++ L2) (Nat.succ j) 0 0 0 0 = _
        rcases Nat.lt_or_ge (j + 1) b with hlt | hge
        · exact run_append hbN L1 L2 (j + 1) 0 0 0 0 hlt h
        · have hb : j + 1 = b := by omega
          subst hb
          cases L1 with
          | nil => rfl
          | cons c' L1' =>
            rw [runX_cons] at h
            have hb' : Nat.beq (Nat.succ j) (j + 1) = true := Nat.beq_refl _
            rw [hb'] at h
            change false = true at h
            exact absurd h Bool.false_ne_true

end CFSG.KC.Misc.HexFlat

end
